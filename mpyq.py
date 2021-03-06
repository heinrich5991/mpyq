#!/usr/bin/env python
# coding: utf-8

"""
mpyq is a Python library for reading MPQ (MoPaQ) archives.
"""

import bz2
from cStringIO import StringIO
import math
import os
import struct
import zlib
from collections import namedtuple


__author__ = "Aku Kotkavuo and heinrich5991"
__version__ = "0.2.0"


MPQ_FILE_IMPLODE        = 0x00000100
MPQ_FILE_COMPRESS       = 0x00000200
MPQ_FILE_ENCRYPTED      = 0x00010000
MPQ_FILE_FIX_KEY        = 0x00020000
MPQ_FILE_SINGLE_UNIT    = 0x01000000
MPQ_FILE_DELETE_MARKER  = 0x02000000
MPQ_FILE_SECTOR_CRC     = 0x04000000
MPQ_FILE_EXISTS         = 0x80000000

MPQFileHeader = namedtuple('MPQFileHeader',
    '''
    magic
    header_size
    archive_size
    format_version
    sector_size_shift
    hash_table_offset
    block_table_offset
    hash_table_entries
    block_table_entries
    '''
)
MPQFileHeader.struct_format = '<4s2I2H4I'

MPQFileHeaderExt = namedtuple('MPQFileHeaderExt',
    '''
    extended_block_table_offset
    hash_table_offset_high
    block_table_offset_high
    '''
)
MPQFileHeaderExt.struct_format = 'q2h'

MPQUserDataHeader = namedtuple('MPQUserDataHeader',
    '''
    magic
    user_data_size
    mpq_header_offset
    user_data_header_size
    '''
)
MPQUserDataHeader.struct_format = '<4s3I'

MPQHashTableEntry = namedtuple('MPQHashTableEntry',
    '''
    hash_a
    hash_b
    locale
    platform
    block_table_index
    '''
)
MPQHashTableEntry.struct_format = '2I2HI'

MPQBlockTableEntry = namedtuple('MPQBlockTableEntry',
    '''
    offset
    archived_size
    size
    flags
    '''
)
MPQBlockTableEntry.struct_format = '4I'

def pad(number, mod):
    return number + (-number % mod)

class MPQCommon:
    @classmethod
    def hash(cls, string, hash_type):
        """Hash a string using MPQ's hash function."""
        hash_types = {
            'TABLE_OFFSET': 0,
            'HASH_A': 1,
            'HASH_B': 2,
            'TABLE': 3
        }
        seed1 = 0x7FED7FED
        seed2 = 0xEEEEEEEE

        for ch in string:
            ch = ord(ch.upper())
            value = cls.encryption_table[(hash_types[hash_type] << 8) + ch]
            seed1 = (value ^ (seed1 + seed2)) & 0xFFFFFFFF
            seed2 = ch + seed1 + seed2 + (seed2 << 5) + 3 & 0xFFFFFFFF

        return seed1

    @classmethod
    def encrypt(cls, data, key):
        """Encrypt hash or block table or a sector."""
        seed1 = key
        seed2 = 0xEEEEEEEE
        result = StringIO()

        for i in range(len(data) // 4):
            seed2 += cls.encryption_table[0x400 + (seed1 & 0xFF)]

            # this isn't required in c, because integers would just wrap
            seed2 &= 0xFFFFFFFF

            value = struct.unpack("<I", data[4*i:4*i+4])[0]
            
            result.write(struct.pack("<I", value ^ ((seed1 + seed2) & 0xFFFFFFFF)))

            seed1 = (((~seed1 << 0x15) + 0x11111111) | (seed1 >> 0xB)) & 0xFFFFFFFF
            seed2 = (value + seed2 + (seed2 << 5) + 3) & 0xFFFFFFFF

        return result.getvalue()

    @classmethod
    def decrypt(cls, data, key):
        """Decrypt hash or block table or a sector."""
        seed1 = key
        seed2 = 0xEEEEEEEE
        result = StringIO()

        for i in range(len(data) // 4):
            seed2 += cls.encryption_table[0x400 + (seed1 & 0xFF)]
            seed2 &= 0xFFFFFFFF
            value = struct.unpack("<I", data[i*4:i*4+4])[0]
            value = (value ^ (seed1 + seed2)) & 0xFFFFFFFF

            seed1 = ((~seed1 << 0x15) + 0x11111111) | (seed1 >> 0x0B)
            seed1 &= 0xFFFFFFFF
            seed2 = value + seed2 + (seed2 << 5) + 3 & 0xFFFFFFFF

            result.write(struct.pack("<I", value))

        return result.getvalue()

    @staticmethod
    def decompress(data):
        """Read the compression type and decompress file data."""
        compression_type = ord(data[0])
        if compression_type == 0:
            return data
        elif compression_type == 2:
            return zlib.decompress(data[1:], 15)
        elif compression_type == 16:
            return bz2.decompress(data[1:])
        else:
            raise RuntimeError("Unsupported compression type.")

    @staticmethod
    def compress(data):
        """Try compressions and return the best one."""
        compressed = []
        compressed.append(chr(16) + bz2.compress(data))
        compressed.append(chr(2) + zlib.compress(data))
        compressed_data = data
        for d in compressed:
            if len(d) < len(compressed_data):
                compressed_data = d

        # correctly compressed?
        assert data == compressed_data or MPQCommon.decompress(compressed_data) == data

        return compressed_data

    @classmethod
    def get_file_extension(cls, content):
        if content:
            for magic_checker in cls.magic_checkers:
                extension = magic_checker(content)
                if extension:
                    return '.' + extension
        return ''

    @classmethod
    def add_filename(cls, filename):
        filename = filename.lower()
        hash_a = cls.hash(filename, 'HASH_A')
        hash_b = cls.hash(filename, 'HASH_B')
        cls.lookup_table[(hash_a, hash_b)] = filename

    @classmethod
    def get_filename(cls, hash_a, hash_b, content=None):
        if (hash_a, hash_b) not in cls.lookup_table:
            return "(%x%x)" % (hash_a, hash_b) + cls.get_file_extension(content)

        return cls.lookup_table[(hash_a, hash_b)]

    @classmethod
    def _prepare_lookup_table(cls):
        cls.lookup_table = {}

        # taken from stormlib
        magic_table_stormlib = (
            (0x00005A4D, 0x0000FFFF, 0x00000000, 0x00000000, "exe"),    # EXE files
            (0x00000006, 0xFFFFFFFF, 0x00000001, 0xFFFFFFFF, "dc6"),    # EXE files
            (0x1A51504D, 0xFFFFFFFF, 0x00000000, 0x00000000, "mpq"),    # MPQ archive header ID ('MPQ\x1A')
            (0x46464952, 0xFFFFFFFF, 0x00000000, 0x00000000, "wav"),    # WAVE header 'RIFF'
            (0x324B4D53, 0xFFFFFFFF, 0x00000000, 0x00000000, "smk"),    # Old "Smacker Video" files 'SMK2'
            (0x694B4942, 0xFFFFFFFF, 0x00000000, 0x00000000, "bik"),    # Bink video files (new)
            (0x0801050A, 0xFFFFFFFF, 0x00000000, 0x00000000, "pcx"),    # PCX images used in Diablo I
            (0x544E4F46, 0xFFFFFFFF, 0x00000000, 0x00000000, "fnt"),    # Font files used in Diablo II
            (0x6D74683C, 0xFFFFFFFF, 0x00000000, 0x00000000, "html"),   # HTML '<htm'
            (0x4D54483C, 0xFFFFFFFF, 0x00000000, 0x00000000, "html"),   # HTML '<HTM
            (0x216F6F57, 0xFFFFFFFF, 0x00000000, 0x00000000, "tbl"),    # Table files
            (0x31504C42, 0xFFFFFFFF, 0x00000000, 0x00000000, "blp"),    # BLP textures
            (0x32504C42, 0xFFFFFFFF, 0x00000000, 0x00000000, "blp"),    # BLP textures (v2)
            (0x584C444D, 0xFFFFFFFF, 0x00000000, 0x00000000, "mdx"),    # MDX files
            (0x45505954, 0xFFFFFFFF, 0x00000000, 0x00000000, "pud"),    # Warcraft II maps
            (0x38464947, 0xFFFFFFFF, 0x00000000, 0x00000000, "gif"),    # GIF images 'GIF8'
            (0x3032444D, 0xFFFFFFFF, 0x00000000, 0x00000000, "m2"),     # WoW ??? .m2
            (0x43424457, 0xFFFFFFFF, 0x00000000, 0x00000000, "dbc"),    # ??? .dbc
            (0x47585053, 0xFFFFFFFF, 0x00000000, 0x00000000, "bls"),    # WoW pixel shaders
            (0xE0FFD8FF, 0xFFFFFFFF, 0x00000000, 0x00000000, "jpg"),    # JPEG image
        )

        def check_magic_stormlib(content):
            dword00, dword04 = struct.unpack('%I%I', content[:4])
            for magic_stormlib in cls.magic_table_stormlib:
                if (dword00 & magic.offset00mask == magic.offset00data and
                    dword04 & magic.offset04mask == magic.offset04data):
                    return magic.extension
            return None

        MagicStormlib = namedtuple('Magic', '''
            offset00data
            offset00mask
            offset04data
            offset04mask
            extension
        ''')

        cls.magic_checkers = []
        cls.magic_table_stormlib = []

        for magic_stormlib in magic_table_stormlib:
            cls.magic_table_stormlib.append(MagicStormlib(*magic_stormlib))

        cls.magic_checkers.append(check_magic_stormlib)


    @classmethod
    def _prepare_encryption_table(cls):
        """Prepare encryption table for MPQ hash function."""
        seed = 0x00100001
        crypt_table = {}

        for i in range(256):
            index = i
            for j in range(5):
                seed = (seed * 125 + 3) % 0x2AAAAB
                temp1 = (seed & 0xFFFF) << 0x10

                seed = (seed * 125 + 3) % 0x2AAAAB
                temp2 = (seed & 0xFFFF)

                crypt_table[index] = (temp1 | temp2)

                index += 0x100

        cls.encryption_table = crypt_table

class MPQArchiveWriter:
    def __init__(self, filename, archive_reader=None):
        if hasattr(filename, 'write'):
            self.file = filename
            self.close_file = False
        else:
            self.file = open(filename, 'wb')
            self.close_file = True

        self.user_data = None
        self.sector_size_shift = 3

        if archive_reader:
            if 'user_data_header' in archive_reader.header:
                self.user_data = archive_reader.header['user_data_header']['content']
            self.sector_size_shift = archive_reader.header['sector_size_shift']

        self.offsets = {}
        self.offsets['start'] = self.file.tell()

        self.hash_table = []
        self.block_table = []
        self.listfile = []

        self.initialised = False

    def _check_initialisation(self):
        if self.initialised:
            return

        self.file.seek(self.offsets['start'])
        if self.user_data:
            self.offsets['userdata'] = pad(self.file.tell(), 512)
            self.file.seek(self.offsets['userdata'])
            self.file.write(struct.calcsize(MPQUserDataHeader.struct_format) * '\x00')
            self.file.write(self.user_data)

        self.offsets['header'] = pad(self.file.tell(), 512)
        self.file.seek(self.offsets['header'])
        self.file.write(struct.calcsize(MPQFileHeader.struct_format) * '\x00')
        self.offsets['data'] = self.file.tell()
        self.offsets['nextdata'] = self.offsets['data']

        if self.user_data:
            self.file.seek(self.offsets['userdata'])
            user_data_header = MPQUserDataHeader(
                magic='MPQ\x1b',
                user_data_size=self.offsets['header']-self.offsets['userdata'],
                mpq_header_offset=self.offsets['header']-self.offsets['userdata'],
                user_data_header_size=len(self.user_data)
            )
            self.file.write(struct.pack(MPQUserDataHeader.struct_format,
                                        *user_data_header))

        self.initialised = True

    def _write_file(self, file, compress=True):
        self._check_initialisation()
        begin_file = self.offsets['nextdata']

        sector_size = 512 << self.sector_size_shift

        if file:
            file.seek(0, 2) # go to the end
            file_size = file.tell()
            file.seek(0)
        else:
            file_size = -512

        flags = 0
        archived_size = 0

        num_sectors = pad(file_size, sector_size) // sector_size

        if num_sectors >= 0:
            flags |= MPQ_FILE_EXISTS
            if compress:
                flags |= MPQ_FILE_COMPRESS

        if num_sectors > 1:
            sector_offsets = [0 for x in range(num_sectors + 1)]

            self.file.seek(begin_file)
            if compress:
                self.file.write(struct.pack('<%dI' % len(sector_offsets), *sector_offsets))

            sector_offsets[0] = self.file.tell() - begin_file
            for s in range(1, len(sector_offsets)):
                data = file.read(sector_size)
                if compress:
                    data = MPQCommon.compress(data)
                self.file.write(data)

                archived_size += len(data)
                sector_offsets[s] = self.file.tell() - begin_file

            self.offsets['nextdata'] = self.file.tell()

            if compress:
                self.file.seek(begin_file)
                self.file.write(struct.pack('<%dI' % len(sector_offsets), *sector_offsets))
                sector_table_size = struct.calcsize('<%dI' % len(sector_offsets))

        elif num_sectors >= 0:
            flags |= MPQ_FILE_SINGLE_UNIT

            self.file.seek(begin_file)
            data = file.read()
            if compress:
                compressed_data = MPQCommon.compress(data)
                if len(compressed_data) < len(data):
                    data = compressed_data
            self.file.write(data)
            archived_size = len(data)

            self.offsets['nextdata'] = self.file.tell()
        else:
            flags |= MPQ_FILE_DELETE_MARKER

        block_table_entry = MPQBlockTableEntry(
            offset=begin_file,
            size=file_size,
            archived_size=archived_size,
            flags=flags
        )

        return block_table_entry

    def add_file_by_hash(self, filename, hash_a, hash_b, locale=0, platform=0, **kwargs):
        close = False
        if filename is None or hasattr(filename, 'read'):
            file = filename
        else:
            file = open(filename, 'rb')
            close = True

        block_table_entry = self._write_file(file, **kwargs)

        if close:
            file.close()

        hash_table_entry = MPQHashTableEntry(
            hash_a=hash_a,
            hash_b=hash_b,
            locale=locale,
            platform=platform,
            block_table_index=len(self.block_table)
        )

        self.hash_table.append(hash_table_entry)
        self.block_table.append(block_table_entry)

    def add_file(self, filename, filename_archive, update_listfile=True, **kwargs):
        """Add a file to the archive by name."""
        self.add_file_by_hash(filename,
                              hash_a=MPQCommon.hash(filename_archive, 'HASH_A'),
                              hash_b=MPQCommon.hash(filename_archive, 'HASH_B'),
                              **kwargs)

        MPQCommon.add_filename(filename_archive)
        if update_listfile:
            self.listfile.append(filename_archive)

    def close(self):
        self._check_initialisation()

        def _get_raw_table_data(table_type, table_entries):
            if table_type == 'hash':
                entry_class = MPQHashTableEntry
            elif table_type == 'block':
                entry_class = MPQBlockTableEntry
            else:
                raise ValueError("Invalid table type.")

            key = MPQCommon.hash('(%s table)' % table_type, 'TABLE')

            table_entries = [struct.pack(entry_class.struct_format, *x)
                             for x in table_entries]
            data = ''.join(table_entries)
            return MPQCommon.encrypt(data, key)

        self.add_file(StringIO('\n'.join(self.listfile) + '\n'),
                      '(listfile)', update_listfile=False)

        self.file.seek(self.offsets['nextdata'])
        del self.offsets['nextdata']

        wanted_hash_table_size = 2 ** (int(math.log(len(self.hash_table) - 1, 2)) + 1)
        for i in range(wanted_hash_table_size - len(self.hash_table)):
            self.hash_table.append(MPQHashTableEntry(
                hash_a=0,
                hash_b=0,
                language=0,
                platform=0,
                block_table_index=0xFFFFFFFF
            ))

        self.offsets['hash_table'] = self.file.tell()
        self.file.write(_get_raw_table_data('hash', self.hash_table))
        self.offsets['block_table'] = self.file.tell()
        self.file.write(_get_raw_table_data('block', self.block_table))
        self.offsets['end'] = self.file.tell()

        self.file.seek(self.offsets['header'])
        header = MPQFileHeader(
            magic='MPQ\x1a',
            header_size=struct.calcsize(MPQFileHeader.struct_format),
            archive_size=self.offsets['end']-self.offsets['header'],
            format_version=0,
            sector_size_shift=self.sector_size_shift,
            hash_table_offset=self.offsets['hash_table']-self.offsets['header'],
            hash_table_entries=len(self.hash_table),
            block_table_offset=self.offsets['block_table']-self.offsets['header'],
            block_table_entries=len(self.block_table)
        )
        self.file.write(struct.pack(MPQFileHeader.struct_format, *header))

        if self.close_file:
            self.file.close()
        self.file = None

class MPQArchiveReader:
    def __init__(self, filename):
        """Open an MPQ archive."""

        if hasattr(filename, 'read'):
            self.file = filename
        else:
            self.file = open(filename, 'rb')
        self.header = self.read_header()
        self.hash_table = self.read_table('hash')
        self.block_table = self.read_table('block')
        listfile = self.read_file('(listfile)')
        if listfile:
            for name in self.read_file('(listfile)').split():
                MPQCommon.add_filename(name.strip())

    def read_header(self):
        """Read the header of a MPQ archive."""

        def read_mpq_header(offset=None):
            if offset:
                self.file.seek(offset)
            data = self.file.read(32)
            header = MPQFileHeader._make(
                struct.unpack(MPQFileHeader.struct_format, data))
            header = header._asdict()
            if header['format_version'] == 1:
                data = self.file.read(12)
                extended_header = MPQFileHeaderExt._make(
                    struct.unpack(MPQFileHeaderExt.struct_format, data))
                header.update(extended_header._asdict())
            return header

        def read_mpq_user_data_header():
            data = self.file.read(16)
            header = MPQUserDataHeader._make(
                struct.unpack(MPQUserDataHeader.struct_format, data))
            header = header._asdict()
            header['content'] = self.file.read(header['user_data_header_size'])
            return header

        magic = self.file.read(4)
        self.file.seek(0)

        if magic == 'MPQ\x1a':
            header = read_mpq_header()
            header['offset'] = 0
        elif magic == 'MPQ\x1b':
            user_data_header = read_mpq_user_data_header()
            header = read_mpq_header(user_data_header['mpq_header_offset'])
            header['offset'] = user_data_header['mpq_header_offset']
            header['user_data_header'] = user_data_header

        return header

    def read_table(self, table_type):
        """Read either the hash or block table of a MPQ archive."""

        if table_type == 'hash':
            entry_class = MPQHashTableEntry
        elif table_type == 'block':
            entry_class = MPQBlockTableEntry
        else:
            raise ValueError("Invalid table type.")

        table_offset = self.header['%s_table_offset' % table_type]
        table_entries = self.header['%s_table_entries' % table_type]
        key = MPQCommon.hash('(%s table)' % table_type, 'TABLE')

        self.file.seek(table_offset + self.header['offset'])
        data = self.file.read(table_entries * 16)
        data = MPQCommon.decrypt(data, key)

        def unpack_entry(position):
            entry_data = data[position*16:position*16+16]
            return entry_class._make(
                struct.unpack(entry_class.struct_format, entry_data))

        return [unpack_entry(i) for i in range(table_entries)]

    def get_hash_table_entry(self, filename):
        """Get the hash table entry corresponding to a given filename."""
        hash_a = MPQCommon.hash(filename, 'HASH_A')
        hash_b = MPQCommon.hash(filename, 'HASH_B')
        for entry in self.hash_table:
            if entry.hash_a == hash_a and entry.hash_b == hash_b:
                return entry

    def read_file(self, filename, **kwargs):
        """Read a file from the MPQ archive."""
        MPQCommon.add_filename(filename)
        hash_entry = self.get_hash_table_entry(filename)
        if hash_entry is None:
            return None
        return self.read_file_by_hashentry(hash_entry, **kwargs)

    def read_file_by_hashentry(self, hash_entry, force_decompress=False):
        block_entry = self.block_table[hash_entry.block_table_index]

        # Read the block.
        if block_entry.flags & MPQ_FILE_EXISTS:
            if block_entry.archived_size == 0:
                return None

            offset = block_entry.offset + self.header['offset']
            self.file.seek(offset)
            file_data = self.file.read(block_entry.archived_size)

            if block_entry.flags & MPQ_FILE_ENCRYPTED:
                raise NotImplementedError("Encryption is not supported yet.")

            if not block_entry.flags & MPQ_FILE_SINGLE_UNIT:
                if block_entry.flags & MPQ_FILE_COMPRESS:
                    # File consist of many sectors. They all need to be
                    # decompressed separately and united.
                    sector_size = 512 << self.header['sector_size_shift']
                    num_sectors = block_entry.size // sector_size + 1
                    num_data_sectors = num_sectors
                    if block_entry.flags & MPQ_FILE_SECTOR_CRC:
                        crc = True
                        num_sectors += 1
                    else:
                        crc = False
                    positions = struct.unpack('<%dI' % (num_sectors + 1),
                                              file_data[:4*(num_sectors+1)])
                    result = StringIO()
                    for i in range(num_data_sectors - 1):
                        sector = file_data[positions[i]:positions[i+1]]
                        if (force_decompress or
                            len(sector) < (sector_size if i < num_data_sectors - 2 else block_entry.size % sector_size)):
                            sector = MPQCommon.decompress(sector)
                        result.write(sector)
                    file_data = result.getvalue()
                else:
                    # Uncompressed files do not have the sector offset table
                    file_data = file_data
            else:
                # Single unit files only need to be decompressed, but
                # compression only happens when at least one byte is gained.
                if (block_entry.flags & MPQ_FILE_COMPRESS and
                    (force_decompress or block_entry.size > block_entry.archived_size)):
                    file_data = MPQCommon.decompress(file_data)

            return file_data

    def extract(self):
        """Extract all the files inside the MPQ archive in memory."""
        return dict((MPQCommon.get_filename(h.hash_a, h.hash_b),
                     self.read_file_by_hashentry(h))
                    for h in self.hash_table)

    def extract_to_disk(self):
        """Extract all files and write them to disk."""
        archive_name, extension = os.path.splitext(os.path.basename(self.file.name))
        if not os.path.isdir(os.path.join(os.getcwd(), archive_name)):
            os.mkdir(archive_name)
        os.chdir(archive_name)
        for h in self.hash_table:
            with open(MPQCommon.get_filename(h.hash_a, h.hash_b), 'wb') as f:
                f.write(self.read_file_by_hashentry(h))

    def extract_files(self, *filenames):
        """Extract given files from the archive to disk."""
        for filename in filenames:
            data = self.read_file(filename)
            f = open(filename, 'wb')
            f.write(data)
            f.close()

    def print_headers(self):
        print "MPQ archive header"
        print "------------------"
        for key, value in self.header.iteritems():
            if key == "user_data_header":
                continue
            print "{0:30} {1!r}".format(key, value)
        if self.header.get('user_data_header'):
            print
            print "MPQ user data header"
            print "--------------------"
            for key, value in self.header['user_data_header'].iteritems():
                print "{0:30} {1!r}".format(key, value)
        print

    def print_hash_table(self):
        print "MPQ archive hash table"
        print "----------------------"
        print " Hash A   Hash B  Locl Plat BlockIdx"
        for entry in self.hash_table:
            print '%08X %08X %04X %04X %08X' % entry
        print

    def print_block_table(self):
        print "MPQ archive block table"
        print "-----------------------"
        print " Offset  ArchSize RealSize  Flags"
        for entry in self.block_table:
            print '%08X %8d %8d %8X' % entry
        print

    def print_files(self):
        if self.files:
            print "Files"
            print "-----"
            width = max(len(name) for name in self.files) + 2
            for filename in self.files:
                hash_entry = self.get_hash_table_entry(filename)
                block_entry = self.block_table[hash_entry.block_table_index]
                print "{0:{width}} {1:>8} bytes".format(filename,
                                                        block_entry.size,
                                                        width=width)

def main():
    import argparse
    description = "mpyq reads and extracts MPQ archives."
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("file", action="store", help="path to the archive")
    parser.add_argument("-I", "--headers", action="store_true", dest="headers",
                        help="print header information from the archive")
    parser.add_argument("-H", "--hash-table", action="store_true",
                        dest="hash_table", help="print hash table"),
    parser.add_argument("-b", "--block-table", action="store_true",
                        dest="block_table", help="print block table"),
    parser.add_argument("-s", "--skip-listfile", action="store_true",
                        dest="skip_listfile", help="skip reading (listfile)"),
    parser.add_argument("-t", "--list-files", action="store_true", dest="list",
                        help="list files inside the archive")
    parser.add_argument("-x", "--extract", action="store_true", dest="extract",
                        help="extract files from the archive")
    args = parser.parse_args()
    if args.file:
        if not args.skip_listfile:
            archive = MPQArchiveReader(args.file)
        else:
            archive = MPQArchiveReader(args.file, listfile=False)
        if args.headers:
            archive.print_headers()
        if args.hash_table:
            archive.print_hash_table()
        if args.block_table:
            archive.print_block_table()
        if args.list:
            archive.print_files()
        if args.extract:
            archive.extract_to_disk()

MPQCommon._prepare_encryption_table()
MPQCommon._prepare_lookup_table()

if __name__ == '__main__':
    main()
