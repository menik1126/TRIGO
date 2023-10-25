import trigo_import
open real
open_locale real
variables (x y : ℝ)


lemma Trigo_0 (h0 : sin(335*pi/4)≠ 0) (h1 : (2*sin(335*pi/4))≠ 0) (h2 : (2*sin(335*pi/4)**2)≠ 0) : cos(7*pi/2)=-sin(335*pi/2)**2/(2*sin(335*pi/4)**2) + 1:=
begin
have : cos (7 * pi / 2)   =  cos(7*pi/2),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(pi)  =  cos(7*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have :  1 - 2 * (sin (335 * pi / 2) / (2 * sin (335 * pi / 4))) ** 2  =  -sin(335*pi/2)**2/(2*sin(335*pi/4)**2) + 1,
{
try {field_simp at *},
try {repeat {left}},
try {ring},
},
conv {to_rhs, rw ← this,},
have : cos(335*pi/4)  =  sin(335*pi/2) / ( 2 * sin(335*pi/4) ),
{
have : sin (335*pi/2) = sin(2*(335*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
try {field_simp at *},
try {ring},
},
conv {to_rhs, rw ← this,},
have :  -(2 * cos (335 * pi / 4) ** 2 - 1)  =  1 - 2*cos(335*pi/4)**2,
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : cos(335*pi/2)  =  2 * cos(335*pi/4) ** 2 - 1,
{
have : cos (335*pi/2) = cos(2*(335*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi)  =  - cos(335*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (83),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
rw this,
end


lemma Trigo_1 : -sin(pi)*cos(2*pi) + sin(2*pi)*cos(3*pi) + sin(-2*pi)=-2*sin(-pi/2)*cos(13*pi/2):=
begin
have : -sin pi * cos (2 * pi) + sin (2 * pi) * cos (3 * pi) + sin ((-2) * pi)   =  -sin(pi)*cos(2*pi) + sin(2*pi)*cos(3*pi) + sin(-2*pi),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(pi)  =  cos(3*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : sin ((-2) * pi) - (sin pi * cos (2 * pi) - sin (2 * pi) * cos pi)   =  -sin(pi)*cos(2*pi) + sin(2*pi)*cos(pi) + sin(-2*pi),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(-pi)  =  sin(pi) * cos(2*pi) - sin(2*pi) * cos(pi),
{
have : sin(-pi) = sin((pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
try {ring},
},
conv {to_lhs, rw ← this,},
have :  2 * sin (-pi / 2) * -cos (13 * pi / 2)  =  -2*sin(-pi/2)*cos(13*pi/2),
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : cos(-3*pi/2)  =  -cos(13*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3*pi/2) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) - sin(-pi)  =  2 * sin(-pi/2) * cos(-3*pi/2),
{
rw sin_sub_sin,
have : cos(((-2*pi) + (-pi))/2) = cos (-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-2*pi) - (-pi))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
try {ring},
},
rw this,
end


lemma Trigo_2 : (-2*sin(-13*pi/8)*cos(5*pi/2) + 2*cos(-13*pi/8)*cos(2*pi))*sin(3*pi/8)=sqrt( 2 ) / 2:=
begin
have : 2 * (-sin ((-13) * pi / 8) * cos (5 * pi / 2) + cos ((-13) * pi / 8) * cos (2 * pi)) * sin (3 * pi / 8)   =  (-2*sin(-13*pi/8)*cos(5*pi/2) + 2*cos(-13*pi/8)*cos(2*pi))*sin(3*pi/8),
{
try {field_simp at *},
try {repeat {left}},
try {ring},
},
conv {to_lhs, rw ← this,},
have : sin(2*pi)  =  cos(5*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin (3 * pi / 8) * (-sin ((-13) * pi / 8) * sin (2 * pi) + cos ((-13) * pi / 8) * cos (2 * pi))   =  2*(-sin(-13*pi/8)*sin(2*pi) + cos(-13*pi/8)*cos(2*pi))*sin(3*pi/8),
{
try {field_simp at *},
try {repeat {left}},
try {ring},
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8)  =  -sin(-13*pi/8) * sin(2*pi) + cos(-13*pi/8) * cos(2*pi),
{
have : cos(3*pi/8) = cos((-13*pi/8) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
try {ring},
},
conv {to_lhs, rw ← this,},
have : 2 * sin (3 * pi / 8) * cos (3 * pi / 8)   =  2*sin(3*pi/8)*cos(3*pi/8),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4)  =  2 * sin(3*pi/8) * cos(3*pi/8),
{
have : sin (3*pi/4) = sin(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4)  =  sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_3 : (-1 + 2*cos(9*pi/2)**2)*cos(-2*pi)=cos(-pi)*cos(2*pi):=
begin
have : (-1 + 2 * cos (9 * pi / 2) ** 2) * cos ((-2) * pi)   =  (-1 + 2*cos(9*pi/2)**2)*cos(-2*pi),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2)  =  cos(9*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have :  1 / 2 * (2 * cos (2 * pi) * cos (-pi))  =  cos(-pi)*cos(2*pi),
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : cos(pi) + cos(-3*pi)  =  2 * cos(2*pi) * cos(-pi),
{
rw cos_add_cos,
have : cos(((pi) + (-3*pi))/2) = cos (-pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (-3*pi))/2) = cos(2*pi),
{
apply congr_arg,
ring,
},
rw this,
try {ring},
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(pi) + cos(-3*pi))  =  cos(pi)/2+cos(-3*pi)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : (2 * cos (-pi / 2) ** 2 - 1) * cos ((-2) * pi)   =  (-1 + 2*cos(-pi/2)**2)*cos(-2*pi),
{
try {field_simp at *},
try {repeat {left}},
try {ring},
},
conv {to_lhs, rw ← this,},
have : cos(-pi)  =  2 * cos(-pi/2) ** 2 - 1,
{
have : cos (-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(-2*pi)  =  cos(pi) / 2 + cos(-3*pi) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (-2*pi)) = cos (-3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-2*pi)) = cos (pi),
{
apply congr_arg,
ring,
},
rw this,
try {ring},
},
rw this,
end


lemma Trigo_4 (h0 : sin(269*pi/2)≠ 0) (h1 : (2*sin(269*pi/2))≠ 0) : -sin(-2*pi)=-sin(269*pi)/(2*sin(269*pi/2)):=
begin
have : -sin ((-2) * pi)   =  -sin(-2*pi),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(15*pi/2)  =  -sin(-2*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (15*pi/2) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : cos (15 * pi / 2)   =  cos(15*pi/2),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(2*pi)  =  cos(15*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have :  -(sin (269 * pi) / (2 * sin (269 * pi / 2)))  =  -sin(269*pi)/(2*sin(269*pi/2)),
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : cos(269*pi/2)  =  sin(269*pi) / ( 2 * sin(269*pi/2) ),
{
have : sin (269*pi) = sin(2*(269*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
try {field_simp at *},
try {ring},
},
conv {to_rhs, rw ← this,},
have : sin(2*pi)  =  - cos(269*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (66),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
rw this,
end


lemma Trigo_5 : sin(3*pi/2)=3*cos(16*pi/3) - 4*cos(16*pi/3)**3:=
begin
have :  4 * (-cos (16 * pi / 3)) ** 3 - 3 * -cos (16 * pi / 3)  =  3*cos(16*pi/3) - 4*cos(16*pi/3)**3,
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : cos(pi/3)  =  -cos(16*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_rhs, rw ← this,},
have : sin (3 * pi / 2)   =  sin(3*pi/2),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(3*pi)  =  sin(3*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : cos (3 * pi)   =  cos(3*pi),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(pi)  =  cos(3*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi)  =  4 * cos(pi/3) ^ 3 - 3 * cos(pi/3),
{
have : cos (pi) = cos(3*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
try {ring},
},
rw this,
end


lemma Trigo_6 : -1 + 2*(cos(2*pi)*cos(3*pi) + sin(2*pi)*sin(3*pi))**2=4 * cos(-2*pi) ^ 3 - 3 * cos(-2*pi):=
begin
have : -1 + 2 * (sin (3 * pi) * sin (2 * pi) + cos (3 * pi) * cos (2 * pi)) ** 2   =  -1 + 2*(cos(2*pi)*cos(3*pi) + sin(2*pi)*sin(3*pi))**2,
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(pi)  =  sin(3*pi) * sin(2*pi) + cos(3*pi) * cos(2*pi),
{
have : cos(pi) = cos((3*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
try {ring},
},
conv {to_lhs, rw ← this,},
have : -1 + 2 * cos pi ** 2   =  -1 + 2*cos(pi)**2,
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi)  =  cos(pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-3*pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos ((-3) * pi) ** 2 - 1   =  -1 + 2*cos(-3*pi)**2,
{
try {field_simp at *},
try {repeat {left}},
try {ring},
},
conv {to_lhs, rw ← this,},
have : cos(-6*pi)  =  2 * cos(-3*pi) ** 2 - 1,
{
have : cos (-6*pi) = cos(2*(-3*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-6*pi)  =  4 * cos(-2*pi) ^ 3 - 3 * cos(-2*pi),
{
have : cos (-6*pi) = cos(3*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
try {ring},
},
rw this,
end


lemma Trigo_7 : sin(0)=0:=
begin
have : sin(0)  =  0,
{
rw sin_zero,
},
rw this,
end


lemma Trigo_8 : (-sin(2*pi)*cos(pi) + (-sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi))*sin(13*pi/2))**2 + cos(-pi)**2=1:=
begin
have : (-sin (2 * pi) * cos pi + (sin (3 * pi) * cos (2 * pi) - sin (2 * pi) * cos (3 * pi)) * sin (13 * pi / 2)) ** 2 +
      cos (-pi) ** 2   =  (-sin(2*pi)*cos(pi) + (-sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi))*sin(13*pi/2))**2 + cos(-pi)**2,
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(pi)  =  sin(3*pi) * cos(2*pi) - sin(2*pi) * cos(3*pi),
{
have : sin(pi) = sin((3*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
try {ring},
},
conv {to_lhs, rw ← this,},
have : (-sin (2 * pi) * cos pi + sin pi * sin (13 * pi / 2)) ** 2 + cos (-pi) ** 2   =  (-sin(2*pi)*cos(pi) + sin(pi)*sin(13*pi/2))**2 + cos(-pi)**2,
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : cos(2*pi)  =  sin(13*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : (sin pi * cos (2 * pi) - sin (2 * pi) * cos pi) ** 2 + cos (-pi) ** 2   =  (-sin(2*pi)*cos(pi) + sin(pi)*cos(2*pi))**2 + cos(-pi)**2,
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(-pi)  =  sin(pi) * cos(2*pi) - sin(2*pi) * cos(pi),
{
have : sin(-pi) = sin((pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
try {ring},
},
conv {to_lhs, rw ← this,},
have : sin(-pi) ^ 2 + cos(-pi) ^ 2  =  1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_9 : cos(4*pi)=(6*sin(-pi/3)*cos(-pi/3) - 32*sin(-pi/3)**3*cos(-pi/3)**3)*cos(pi/2) + sin(pi/2)*cos(-2*pi):=
begin
have : 
    (3 * (2 * sin (-pi / 3) * cos (-pi / 3)) - 4 * (2 * sin (-pi / 3) * cos (-pi / 3)) ** 3) * cos (pi / 2) +
      sin (pi / 2) * cos ((-2) * pi)  =  (6*sin(-pi/3)*cos(-pi/3) - 32*sin(-pi/3)**3*cos(-pi/3)**3)*cos(pi/2) + sin(pi/2)*cos(-2*pi),
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/3)  =  2 * sin(-pi/3) * cos(-pi/3),
{
have : sin (-2*pi/3) = sin(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : 
    ((-4) * sin ((-2) * pi / 3) ** 3 + 3 * sin ((-2) * pi / 3)) * cos (pi / 2) + sin (pi / 2) * cos ((-2) * pi)  =  (3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3)*cos(pi/2) + sin(pi/2)*cos(-2*pi),
{
try {field_simp at *},
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi)  =  -4 * sin(-2*pi/3) ** 3 + 3 * sin(-2*pi/3),
{
have : sin (-2*pi) = sin(3*(-2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
try {ring},
},
conv {to_rhs, rw ← this,},
have : cos (4 * pi)   =  cos(4*pi),
{
try {field_simp at *},
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2)  =  cos(4*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/2) (2),
focus{repeat {apply congr_arg _}},
try {simp},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2)  =  sin(-2*pi) * cos(pi/2) + sin(pi/2) * cos(-2*pi),
{
have : sin(-3*pi/2) = sin((-2*pi) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
try {ring},
},
rw this,
end

