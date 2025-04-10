macro_rules! ops_impl {
    (
        $op_trait:ident,
        $op_func:ident,
        $op:tt,
        LHS = $lhs:ty,
        RHS = $rhs:ty,
        OUTPUT = $output:ty
    ) => {
        impl $op_trait<&$rhs> for &$lhs {
            type Output = $output;

            fn $op_func(self, rhs: &$rhs) -> $output {
                *self $op *rhs
            }
        }

        impl $op_trait<&$rhs> for $lhs {
            type Output = $output;

            fn $op_func(self, rhs: &$rhs) -> $output {
                self $op *rhs
            }
        }

        impl $op_trait<$rhs> for &$lhs {
            type Output = $output;

            fn $op_func(self, rhs: $rhs) -> $output {
                *self $op rhs
            }
        }
    };
    (
        $op_trait:ident,
        $op_func:ident,
        $op:tt,
        $assign_trait:ident,
        $assign_func:ident,
        $assign_op:tt,
        LHS = $lhs:ty,
        RHS = $rhs:ty,
        OUTPUT = $output:ty
    ) => {
        impl $op_trait<$rhs> for $lhs {
            type Output = $output;

            fn $op_func(self, rhs: $rhs) -> $output {
                let mut result = self;
                result $assign_op rhs;
                result
            }
        }

        impl $op_trait<&$rhs> for $lhs {
            type Output = $output;

            fn $op_func(self, rhs: &$rhs) -> $output {
                self $op *rhs
            }
        }

        impl $op_trait<$rhs> for &$lhs {
            type Output = $output;

            fn $op_func(self, rhs: $rhs) -> $output {
                *self $op rhs
            }
        }

        impl $op_trait<&$rhs> for &$lhs {
            type Output = $output;

            fn $op_func(self, rhs: &$rhs) -> $output {
                *self $op *rhs
            }
        }

        impl $assign_trait<&$rhs> for $lhs {
            fn $assign_func(&mut self, rhs: &$rhs) {
                *self $assign_op *rhs
            }
        }
    };
}

macro_rules! bytes_impl {
    ($name:ident, $tobytesfunc:expr, $frombytesfunc:expr) => {
        impl From<$name> for Vec<u8> {
            fn from(value: $name) -> Vec<u8> {
                Self::from(&value)
            }
        }

        impl From<&$name> for Vec<u8> {
            fn from(value: &$name) -> Vec<u8> {
                $tobytesfunc(value).to_vec()
            }
        }

        impl TryFrom<Vec<u8>> for $name {
            type Error = String;

            fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
                Self::try_from(&value[..])
            }
        }

        impl TryFrom<&Vec<u8>> for $name {
            type Error = String;

            fn try_from(value: &Vec<u8>) -> Result<Self, Self::Error> {
                Self::try_from(&value[..])
            }
        }

        impl TryFrom<Box<[u8]>> for $name {
            type Error = String;

            fn try_from(value: Box<[u8]>) -> Result<Self, Self::Error> {
                Self::try_from(&value[..])
            }
        }

        impl TryFrom<&[u8]> for $name {
            type Error = String;

            fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
                $frombytesfunc(value)
            }
        }
    };
}

macro_rules! serde_impl {
    ($name:ident, $serfunc:expr, $deserfunc:expr, $len:expr) => {
        impl serdect::serde::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serdect::serde::Serializer,
            {
                let bytes = $serfunc(self);
                serdect::array::serialize_hex_lower_or_bin(&bytes, serializer)
            }
        }

        impl<'de> serdect::serde::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serdect::serde::Deserializer<'de>,
            {
                let mut bytes = [0u8; $len];
                serdect::array::deserialize_hex_or_bin(&mut bytes, deserializer)?;
                $deserfunc(&bytes)
            }
        }
    };
}
