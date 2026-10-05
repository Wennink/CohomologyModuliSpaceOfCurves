# -*- coding: utf-8 -*-
r"""
Convenience tools for handling deprecations.

Most of the code is taken from the SageMath source code in misc/superseded.py
"""
########################################################################
#       Copyright (C) 2012 William Stein <wstein@gmail.com>
#                     2009 Mike Hansen
#                     2009 Florent Hivert
#                     2011 Luca De Feo
#                     2021 Vincent Delecroix <vincent.delecroix@u-bordeaux.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  https://www.gnu.org/licenses/
########################################################################

from warnings import warn
import inspect

from sage.misc.lazy_attribute import lazy_attribute


def merge_request_url(num):
    return "https://gitlab.com/modulispaces/admcycles/-/merge_requests/{}".format(num)


def deprecation(merge_request, message, stacklevel=3):
    message += '\n'
    message += 'See {} for details.'.format(merge_request_url(merge_request))

    # Stack level 3 to get the line number of the code which called
    # the deprecated function which called this function.
    warn(message, DeprecationWarning, stacklevel)


class DeprecatedFunctionAlias:
    """
    A wrapper around methods or functions which automatically prints a
    deprecation message.
    """

    def __init__(self, merge_request, func, module, instance=None, unbound=None):
        try:
            self.__dict__.update(func.__dict__)
        except AttributeError:
            pass  # Cython classes don't have __dict__
        self.merge_request = merge_request
        self.func = func
        self.instance = instance  # for use with methods
        self.unbound = unbound
        self.__module__ = module
        if isinstance(func, type(deprecation)):
            sphinxrole = "func"
        else:
            sphinxrole = "meth"
        doc = 'Deprecated: '
        doc += 'Use :' + sphinxrole + ':`' + self.func.__name__ + '` instead.\n'
        doc += 'See {} for details.\n\n'.format(merge_request_url(merge_request))
        self.__doc__ = doc

    @lazy_attribute
    def __name__(self):
        # first look through variables in stack frames
        for frame in inspect.stack():
            for name, obj in frame[0].f_globals.items():
                if obj is self:
                    return name
        # then search object that contains self as method
        import gc
        import copy
        gc.collect()

        def is_class(gc_ref):
            if not isinstance(gc_ref, dict):
                return False
            is_python_class = '__module__' in gc_ref or '__package__' in gc_ref
            is_cython_class = '__new__' in gc_ref
            return is_python_class or is_cython_class
        search_for = self if (self.unbound is None) else self.unbound
        for ref in gc.get_referrers(search_for):
            if is_class(ref) and ref is not self.__dict__:
                ref_copy = copy.copy(ref)
                for key, val in ref_copy.items():
                    if val is search_for:
                        return key
        raise AttributeError("The name of this deprecated function cannot be determined")

    def __call__(self, *args, **kwds):
        if self.instance is None and self.__module__ != self.func.__module__:
            other = self.func.__module__ + "." + self.func.__name__
        else:
            other = self.func.__name__

        deprecation(self.merge_request,
                    "{} is deprecated. Please use {} instead.".format(
                        self.__name__, other))
        if self.instance is None:
            return self.func(*args, **kwds)
        else:
            return self.func(self.instance, *args, **kwds)

    def __get__(self, inst, cls=None):
        if inst is None:
            return self  # Unbound method lookup on class
        else:
            # Return a bound method wrapper
            return DeprecatedFunctionAlias(self.merge_request, self.func,
                                           self.__module__, instance=inst,
                                           unbound=self)


def deprecated_function_alias(merge_request, func):
    """
    Create an aliased version of a function or a method which raises a
    deprecation warning message.

    If f is a function or a method, write
    ``g = deprecated_function_alias(merge_request, f)``
    to make a deprecated aliased version of f.

    INPUT:

    - ``merge_request`` -- integer. The merge request number where the
      deprecation is introduced.

    - ``func`` -- the function or method to be aliased

    EXAMPLES::

        sage: from admcycles.superseded import deprecated_function_alias
        sage: g = deprecated_function_alias(13, number_of_partitions)
        sage: g(5)
        doctest:...: DeprecationWarning: g is deprecated. Please use sage.combinat.partition.number_of_partitions instead.
        See https://gitlab.com/modulispaces/admcycles/-/merge_requests/13 for details.
        7
    """
    module_name = None
    frame0 = inspect.currentframe()
    if frame0:
        frame1 = frame0.f_back
        if frame1:
            module_name = inspect.getmodulename(frame1.f_code.co_filename)
    if module_name is None:
        module_name = '__main__'
    return DeprecatedFunctionAlias(merge_request, func, module_name)
