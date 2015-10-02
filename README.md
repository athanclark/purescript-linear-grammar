PureScript Linear Grammar
=========================

Just some simple ASTs and DSLs for working with and creating linear equations,
symbolically representing variables as `Map`s from their variable name to their
coefficient value. The structure remains polymorphic, but is intended for
the `Rational`s (and of course, any linear variable type supporting `Ord`).
