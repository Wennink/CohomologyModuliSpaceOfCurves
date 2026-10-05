# -*- coding: utf-8 -*-

import os
import pickle
import bz2
import warnings
import urllib.parse
from urllib.request import urlretrieve, urlopen
from urllib.error import HTTPError
import configparser
import string

from sage.rings.rational_field import QQ
from sage.modules.free_module_element import vector
from sage.misc.cachefunc import CachedFunction, dict_key
from sage.misc.decorators import decorator_keywords
try:
    # NOTE: moved in sage 9.7
    from sage.misc.instancedoc import instancedoc
except ImportError:
    from sage.docs.instancedoc import instancedoc


@instancedoc
class FileCachedFunction(CachedFunction):
    r"""
    Function wrapper that implements a cache extending SageMath's CachedFunction.

    Preface a function definition with @file_cached_function to wrap it.  When
    the wrapped function is called the following locations are visited to try
    and obtain the output data:

    - first the cache in working memory
    - then the local filesystem
    - then the internet If the data is not stored in any of these locations
      then the wrapped function is executed.  The output of the function is
      saved in the working memory cache and as a file in the filesystem.

    By default, the file is saved in the directory given by the directory
    argument in the current working directory.  If a name for a environment
    variable is supplied via the env_var argument and this environment variable
    is set to a valid path, then this director is used instead of the current
    working directory.

    A filename is generated from the function arguments.  The default
    implementation requires that:

    - the arguments are hashable and convertible to strings via str(),
    - the resulting strings do not contain any characters not allowed in file
      names.

    The remote_database_list accepts the url of a file that should contain a
    list of all files in the remote cache, one file per line.
    This allows bulk downloading the files with the download_all() method.

    The key argument accepts a callable to generate the cache key from the
    function arguments. For details see the documentation of CachedFunction.

    The filename argument accepts a callable that generates the file name from
    the function name and the key.  Whenever key is provided, filename must be
    provided, too.

    EXAMPLES::

        sage: from admcycles.file_cache import file_cached_function, ignore_args_key, ignore_args_filename
        sage: from tempfile import mkdtemp
        sage: from shutil import rmtree
        sage: import os

        sage: tmpdir = mkdtemp()
        sage: # We ignore the second argument for caching
        sage: @file_cached_function(directory=tmpdir, key=ignore_args_key([1]), filename=ignore_args_filename())
        ....: def f(a, b=True):
        ....:     pass
        sage: f(1)
        sage: assert os.path.exists(os.path.join(tmpdir, "f_1.pkl.bz2"))
        ....:
        sage: os.environ["TEST_CACHE_DIR"] = tmpdir
        sage: @file_cached_function(directory="", env_var="TEST_CACHE_DIR")
        ....: def f(a, b=True):
        ....:     pass
        sage: f(1)
        sage: assert os.path.exists(os.path.join(tmpdir, "f_1_True.pkl.bz2"))
        sage: rmtree(tmpdir)
    """
    def __init__(self, f, directory, url=None, remote_database_list=None, env_var=None, key=None, filename=None, pickle_wrappers=(None, None)):
        self.env_var = env_var
        if env_var is not None:
            try:
                env_dir = os.environ[env_var]
                if not os.path.isdir(env_dir):
                    warnings.warn("%s=%s is not a directory. Ignoring it." % env_var, env_dir)
                else:
                    directory = os.path.join(env_dir, directory)
            except KeyError:
                pass

        if key is not None and filename is None:
            raise ValueError("If key is provided, filename must also be provided")

        super(FileCachedFunction, self).__init__(f, key=key)
        self.directory = directory
        self.url = url
        self.remote_database_list = remote_database_list
        if self.url is None:
            self.go_online = False
        else:
            self.go_online = self.__get_online_lookup_default()
        self.filename = filename
        self.pickle_wrapper, self.unpickle_wrapper = pickle_wrappers

    def __call__(self, *args, **kwds):
        k = self.get_key(*args, **kwds)

        # First try to return the value from the cache.
        try:
            return self.cache[k]
        except TypeError:  # k is not hashable
            k = dict_key(k)
            try:
                return self.cache[k]
            except KeyError:
                pass
        except KeyError:
            pass

        # If the value is not in the cache, check if the cache file exists.
        # If not, maybe try to download it
        # Note: We prefix the filename with the function name to avoid collisions if mutliple
        # functions are cached in the same directory.
        (filename, filename_with_path) = self.filename_from_args(k)
        if not os.path.exists(filename_with_path) and self.go_online:
            try:
                self.__download(filename, filename_with_path)
            except IOError:
                pass

        # If the cache file exists now, try to load it.
        if os.path.exists(filename_with_path):
            try:
                dat = self.__load_from_file(filename_with_path)
                self.cache[k] = dat
                return dat
            except EOFError:
                print("end of file error, deleting the file and trying again")
                self.remove_file(*args, **kwds)
                return self.__call__(*args, **kwds)
            except IOError:
                pass
            except TypeError:
                warnings.warn("can not unpickle file %s, it was probably created with a newer version of SageMath.")

        # If we reach this, then all methods to retrive the data from the cache have failed.
        dat = self.f(*args, **kwds)
        self.__save(k, dat)
        return dat

    def __config_file(self):
        r"""
        Returns the path to the configuration file.
        """
        return os.path.join(self.directory, "filecache.ini")

    def __get_online_lookup_default(self):
        r"""
        Tries to obtain a user specified value from the config file.
        Returns True if this is not possible.
        """
        cf = self.__config_file()
        config = configparser.ConfigParser()
        config.read(cf)
        try:
            if config[self.f.__name__]['online_lookup'] == 'no':
                return False
        except KeyError:
            pass
        return True

    def set_online_lookup_default(self, b):
        r"""
        Saves the default for online lookup in the configuration file.
        """
        self.set_online_lookup(b)
        cf = self.__config_file()
        config = configparser.ConfigParser()
        config.read(cf)
        if b:
            config[self.f.__name__] = {'online_lookup': 'yes'}
        else:
            config[self.f.__name__] = {'online_lookup': 'no'}
        with open(cf, "w") as configfile:
            config.write(configfile)

    def set_online_lookup(self, b):
        r"""
        Temporarily set whether online lookup is active.
        Use func:`set_online_lookup_default` to save a default.

        It is set to the boolean ``b``.
        """
        if b and self.url is None:
            raise ValueError("no online database available for this function")
        self.go_online = b

    def file_exists(self, *args, **kwds):
        k = self.get_key(*args, **kwds)
        return os.path.exists(self.filename_from_args(k)[1])

    def remove_file(self, *args, **kwds):
        k = self.get_key(*args, **kwds)
        os.remove(self.filename_from_args(k)[1])
        return

    def set_cache(self, dat, *args, **kwds):
        r"""
        Manually add a value to the cache.

        EXAMPLES::

            sage: from admcycles.file_cache import file_cached_function
            sage: from tempfile import mkdtemp
            sage: from shutil import rmtree
            sage: tmpdir = mkdtemp()
            sage: @file_cached_function(directory=tmpdir)
            ....: def f(a, b=True):
            ....:     pass
            sage: f.set_cache("test", 1, b=False)
            sage: assert f(1, False) == "test"  # This is the cached value
            sage: f.clear_cache()
            sage: f(1, False)
            'test'
            sage: rmtree(tmpdir)

            The above output "test" is the file cached value, as f returns None.
        """
        k = self.get_key(*args, **kwds)
        self.__save(k, dat)

    def __create_directory(self):
        r"""
        Creates the directory if it does not exist yet.
        May throw an OSError.
        """
        try:
            try:
                if not os.path.isdir(self.directory):
                    os.mkdir(self.directory)
            except OSError as e:
                if str(e)[:9] == '[Errno 2]':
                    from pathlib import Path
                    Path(self.directory).mkdir(parents=True)
                else:
                    raise e
        except OSError as e:
            if str(e)[:10] == '[Errno 17]':
                # directory already exists, can happen when multiprocessing
                pass
            else:
                print("Can not create directory", self.directory, e)
                raise e

    def __save(self, k, dat):
        r"""
        Saves the data in the cache file and the in-memory cache.

        EXAMPLES::

            sage: from admcycles.file_cache import file_cached_function
            sage: from tempfile import mkdtemp
            sage: from shutil import rmtree
            sage: tmpdir = mkdtemp()
            sage: @file_cached_function(directory=tmpdir)
            ....: def f(a, b=True):
            ....:     pass
            sage: k = f.get_key(1)
            sage: f._FileCachedFunction__save(k, "test")
            sage: assert f.cache[k] == "test"
            sage: f.clear_cache()
            sage: f(1)
            'test'
            sage: rmtree(tmpdir)

            The above "test" is the file cached value, as f returns None.
        """
        self.cache[k] = dat

        (filename, filename_with_path) = self.filename_from_args(k)
        try:
            self.__create_directory()
        except OSError:
            return
        with bz2.open(filename_with_path, 'wb') as f:
            # We force pickle to use protocol version 3 to make
            # sure that it works for all Python 3 version
            # See
            # https://docs.python.org/3/library/pickle.html
            if self.pickle_wrapper is not None:
                dat = self.pickle_wrapper(dat)
            pickle.dump(dat, f, protocol=3)

    def filename_from_args(self, k):
        r"""
        Constructs a file name of the form func_name_arg1_arg2_arg3.pkl.bz2

        EXAMPLES::

            sage: from admcycles.file_cache import file_cached_function
            sage: @file_cached_function(directory="dir")
            ....: def f(a, b=True):
            ....:     pass
            sage: k = f.get_key(1)
            sage: f.filename_from_args(k)
            ('f_1_True.pkl.bz2', 'dir/f_1_True.pkl.bz2')
        """
        if self.filename is None:
            filename = self.f.__name__
            for a in k[0]:
                filename += '_' + str(a)
            filename += '.pkl.bz2'
        else:
            filename = self.filename(self.f, k)
        filename_with_path = os.path.join(self.directory, filename)
        return (filename, filename_with_path)

    def __load_from_file(self, filename_with_path):
        r"""
        Unplickles the given file and returns the data.
        """
        with bz2.open(filename_with_path, 'rb') as file:
            if self.unpickle_wrapper is None:
                return pickle.load(file)
            else:
                return self.unpickle_wrapper(pickle.load(file))

    def __download(self, filename, filename_with_path):
        r"""
        Download the given file from the remote database and stores it
        on the file system.
        """
        if self.url is None:
            raise ValueError('no url provided')
        try:
            self.__create_directory()
        except OSError:
            return
        complete_url = urllib.parse.urljoin(self.url, filename)
        try:
            urlretrieve(complete_url, filename_with_path)
        except HTTPError:
            pass

    def download_all(self):
        r"""
        Download all files from the remote database.
        """
        if self.url is None:
            raise ValueError('no url provided')
        if self.remote_database_list is None:
            raise ValueError('no remote database list provided')
        try:
            for filename in urlopen(self.remote_database_list):
                filename = filename.decode('utf-8').strip()
                # Check that the filename does not contain any characters that
                # may result in downloading from or saving to an unwanted location.
                allowed = set(string.ascii_letters + string.digits + '.' + '_')
                if not set(filename) <= allowed:
                    print("Recived an invalid filename, aborting.")
                    return
                filename_with_path = os.path.join(self.directory, filename)
                if not os.path.exists(filename_with_path):
                    print("Downloading", filename)
                    self.__download(filename, filename_with_path)
        except HTTPError as e:
            print("Can not open", self.remote_database_list, e)


file_cached_function = decorator_keywords(FileCachedFunction)


def ignore_args_key(ignore_args):
    r"""
    Returns a callable that builds a key from a list of arguments,
    but ignores the arguments with the indices supplied by ignore_arguments.

    EXAMPLES::

        sage: from admcycles.file_cache import ignore_args_key
        sage: key = ignore_args_key([0, 1])
        sage: key("first arg", "second arg", "third arg")
        ('third arg',)
    """
    def key(*args, **invalid_args):
        return tuple(arg for i, arg in enumerate(args) if i not in ignore_args)

    return key


def ignore_args_filename():
    r"""
    Returns a callable that builds a file name from the key returned by
    ignore_args_key.

    EXAMPLES::

        sage: from admcycles.file_cache import ignore_args_key, ignore_args_filename
        sage: key = ignore_args_key([0, 1])
        sage: filename = ignore_args_filename()
        sage: def test():
        ....:     pass
        sage: filename(test, key("first arg", "second arg", "third arg"))
        'test_third arg.pkl.bz2'
    """
    def filename(f, key):
        filename = f.__name__
        for a in key:
            filename += '_' + str(a)
        filename += '.pkl.bz2'
        return filename

    return filename


def rational_to_py(q):
    r"""
    Converts a rational number to a pair of python integers.

    EXAMPLES::

        sage: from admcycles.file_cache import rational_to_py
        sage: a, b = rational_to_py(QQ(1/2))
        sage: a
        1
        sage: type(a)
        <class 'int'>
        sage: b
        2
        sage: type(b)
        <class 'int'>
    """
    return (int(q.numerator()), int(q.denominator()))


def py_to_rational(t):
    r"""
    Converts a pair of python integers (a,b) into the rational number a/b.

    EXAMPLES::

        sage: from admcycles.file_cache import py_to_rational
        sage: q = py_to_rational((1, 2))
        sage: q
        1/2
        sage: type(q)
        <class 'sage.rings.rational.Rational'>
    """
    return QQ(t[0]) / QQ(t[1])


def rational_vectors_to_py(vs):
    r"""
    Converts a list of vectors over QQ into a list of tuples of pairs of python integers.

    EXAMPLES::

        sage: from admcycles.file_cache import rational_vectors_to_py
        sage: v = rational_vectors_to_py([vector(QQ, [1/2, 1])])
        sage: v
        [((1, 2), (1, 1))]
    """
    return [tuple(rational_to_py(a) for a in v) for v in vs]


def py_to_rational_vectors(vs):
    r"""
    Converts a list of tuples of pairs of python integers into a list of sparse vectors over QQ.

    EXAMPLES::

        sage: from admcycles.file_cache import py_to_rational_vectors
        sage: v = py_to_rational_vectors([((1, 2), (1, 1))])
        sage: v
        [(1/2, 1)]
        sage: type(v[0])
        <class 'sage.modules.free_module_element.FreeModuleElement_generic_sparse'>
    """
    return [vector(QQ, (py_to_rational(q) for q in v), sparse=True) for v in vs]
