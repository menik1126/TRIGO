import trigo_import
open real
open_locale real
variables (x y : ℝ)


lemma Trigo_0_test : cos(349*pi/2)=sin(-pi) * sin(pi/2) + cos(-pi) * cos(pi/2):=
begin
have : cos(-3*pi/2) = cos(349*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-3*pi/2) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = sin(-pi) * sin(pi/2) + cos(-pi) * cos(pi/2),
{
have : cos(-3*pi/2) = cos((-pi) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_1_test : sin(-2*pi)=-sin(98*pi):=
begin
have : cos(145*pi/2) = -sin(98*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (145*pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = cos(145*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_2_test (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) : 2*tan(pi/12)/(1 - tan(pi/12)**2)=1 / tan(7*pi/3):=
begin
have : tan(pi/6) = 2 * tan(pi/12) / ( 1 - tan(pi/12) ** 2 ),
{
have : tan(pi/6) = tan(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(7*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_3_test : sin(-pi) + sin(2*pi)=2*(sin(-2*pi)*sin(-pi/2) + cos(-2*pi)*cos(-pi/2))*sin(pi/2):=
begin
have : 2 * sin(pi / 2) * (sin((-2) * pi) * sin(-pi / 2) + cos((-2) * pi) * cos(-pi / 2)) = 2*(sin(-2*pi)*sin(-pi/2) + cos(-2*pi)*cos(-pi/2))*sin(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-3*pi/2) = sin(-2*pi) * sin(-pi/2) + cos(-2*pi) * cos(-pi/2),
{
have : cos(-3*pi/2) = cos((-2*pi) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) + sin(2*pi) = 2 * sin(pi/2) * cos(-3*pi/2),
{
rw sin_add_sin,
have : sin(((-pi) + (2*pi))/2) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (2*pi))/2) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_4_test : sin(pi/6)=-1 + 2*sin(244*pi/3)**2:=
begin
have : -(1 - 2 * sin(244 * pi / 3) ** 2) = -1 + 2*sin(244*pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(488*pi/3) = 1 - 2 * sin(244*pi/3) ** 2,
{
have : cos(488*pi/3) = cos(2*(244*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(488*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_6_test : sin(pi/3)=-sin(514*pi/3):=
begin
have : cos(467*pi/6) = -sin(514*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (467*pi/6) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = cos(467*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_8_test : 2*sin(-pi/6)*cos(-pi/6)=- cos(731*pi/6):=
begin
have : sin(-pi/3) = 2 * sin(-pi/6) * cos(-pi/6),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - cos(731*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_10_test (h0 : cos(4*pi/3)≠ 0) (h1 : cos(pi/3)≠ 0) (h2 : (1+tan(4*pi/3)*tan(pi/3))≠ 0) (h3 : (1+tan(pi/3)*tan(4*pi/3))≠ 0) : (-tan(pi/3) + tan(4*pi/3))/(1 + tan(pi/3)*tan(4*pi/3))=- 1 / tan(113*pi/2):=
begin
have : (tan(4 * pi / 3) - tan(pi / 3)) / (1 + tan(4 * pi / 3) * tan(pi / 3)) = (-tan(pi/3) + tan(4*pi/3))/(1 + tan(pi/3)*tan(4*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(4*pi/3) - tan(pi/3) ) / ( 1 + tan(4*pi/3) * tan(pi/3) ),
{
have : tan(pi) = tan((4*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(113*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_12_test (h0 : tan(27*pi)≠ 0) : -1/tan(27*pi)=tan(77*pi/2):=
begin
have : (-1) / tan(27 * pi) = -1/tan(27*pi),
{
field_simp at *,
},
have : tan(pi/2) = -1 / tan(27*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = tan(77*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_14_test : -sin(101*pi/3)=- sin(2*pi) * sin(pi/6) + cos(2*pi) * cos(pi/6):=
begin
have : cos(13*pi/6) = -sin(101*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/6) = - sin(2*pi) * sin(pi/6) + cos(2*pi) * cos(pi/6),
{
have : cos(13*pi/6) = cos((2*pi) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_15_test : -cos(172*pi)=cos(67*pi):=
begin
have : cos(-pi) = -cos(172*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(67*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_17_test : sin(-2*pi/3)=sin(pi/3)*cos(-pi) + (-3*cos(pi/9) + 4*cos(pi/9)**3)*sin(-pi):=
begin
have : sin(pi / 3) * cos(-pi) + sin(-pi) * (4 * cos(pi / 9) ** 3 - 3 * cos(pi / 9)) = sin(pi/3)*cos(-pi) + (-3*cos(pi/9) + 4*cos(pi/9)**3)*sin(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = 4 * cos(pi/9) ** 3 - 3 * cos(pi/9),
{
have : cos(pi/3) = cos(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/3) = sin(pi/3) * cos(-pi) + sin(-pi) * cos(pi/3),
{
have : sin(-2*pi/3) = sin((pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_18_test (h0 : cos(pi/6)≠ 0) : tan(pi/6)=sin(481*pi/6)/cos(pi/6):=
begin
have : sin(pi/6) = sin(481*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_19_test : cos(190*pi)**2=1 / 2 - cos(pi) / 2:=
begin
have : sin(pi/2) = cos(190*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) ** 2 = 1 / 2 - cos(pi) / 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_20_test : cos(231*pi/2)=- sin(171*pi):=
begin
have : sin(2*pi) = cos(231*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(171*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_21_test : sin(5*pi/4)*cos(pi/2) - sin(pi/2)*cos(5*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(5*pi/4) * cos(pi/2) - sin(pi/2) * cos(5*pi/4),
{
have : sin(3*pi/4) = sin((5*pi/4) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_22_test : sin(130*pi/3)=sin(82*pi/3):=
begin
have : sin(-pi/3) = sin(130*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(82*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_24_test : cos(pi)=-sin(211*pi/2)**2 + cos(pi/2)**2:=
begin
have : -(-sin(211 * pi / 2)) ** 2 + cos(pi / 2) ** 2 = -sin(211*pi/2)**2 + cos(pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = -sin(211*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = - sin(pi/2) ** 2 + cos(pi/2) ** 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_25_test : sin(129*pi/2)=4 * cos(-2*pi) ** 3 - 3 * cos(-2*pi):=
begin
have : cos(-6*pi) = sin(129*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-6*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-6*pi) = 4 * cos(-2*pi) ** 3 - 3 * cos(-2*pi),
{
have : cos(-6*pi) = cos(3*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_26_test : sin(pi/2)*cos(129*pi)=- sin(pi/2) / 2 + sin(3*pi/2) / 2:=
begin
have : cos(pi) = cos(129*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(pi) = - sin(pi/2) / 2 + sin(3*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi) + (pi/2)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/2)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_27_test (h0 : (1-2*sin(-pi/2)**2)≠ 0) : sin(-pi)/(1 - 2*sin(-pi/2)**2)=tan(-pi):=
begin
have : cos(-pi) = 1 - 2 * sin(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-pi) / cos(-pi) = tan(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_28_test (h0 : (1-2*sin(-pi)**2)≠ 0) : tan(-2*pi)=sin(-2*pi)/(1 - 2*sin(-pi)**2):=
begin
have : sin((-2) * pi) / (1 - 2 * sin(-pi) ** 2) = sin(-2*pi)/(1 - 2*sin(-pi)**2),
{
field_simp at *,
},
have : cos(-2*pi) = 1 - 2 * sin(-pi) ** 2,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_29_test : sin(-pi/6) - sin(-pi/3)=2*(cos(pi/4)*cos(pi/2) + sin(pi/4)*sin(pi/2))*sin(pi/12):=
begin
have : 2 * sin(pi / 12) * (sin(pi / 4) * sin(pi / 2) + cos(pi / 4) * cos(pi / 2)) = 2*(cos(pi/4)*cos(pi/2) + sin(pi/4)*sin(pi/2))*sin(pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = sin(pi/4) * sin(pi/2) + cos(pi/4) * cos(pi/2),
{
have : cos(-pi/4) = cos((pi/4) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) - sin(-pi/3) = 2 * sin(pi/12) * cos(-pi/4),
{
rw sin_sub_sin,
have : cos(((-pi/6) + (-pi/3))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (-pi/3))/2) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_30_test : 3*sin(-pi/6) - 4*sin(-pi/6)**3=sin(399*pi/2):=
begin
have : (-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6) = 3*sin(-pi/6) - 4*sin(-pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(399*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_31_test (h0 : tan(133*pi/6)≠ 0) : 1/tan(133*pi/6)=1 / tan(241*pi/6):=
begin
have : tan(pi/3) = 1 / tan(133*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(241*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_32_test : -sin(379*pi/6)*cos(-pi)=cos(-2*pi/3) / 2 + cos(-4*pi/3) / 2:=
begin
have : cos(-pi) * -sin(379 * pi / 6) = -sin(379*pi/6)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(379*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(-pi/3) = cos(-2*pi/3) / 2 + cos(-4*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (-pi/3)) = cos(-4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-pi/3)) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_33_test : -cos(409*pi/6)=sin(pi) * cos(pi/3) + sin(pi/3) * cos(pi):=
begin
have : sin(4*pi/3) = -cos(409*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/3) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/3) = sin(pi) * cos(pi/3) + sin(pi/3) * cos(pi),
{
have : sin(4*pi/3) = sin((pi) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_34_test : -cos(145*pi/2)=0:=
begin
have : sin(pi) = -cos(145*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_35_test : -cos(433*pi/3) + sin(pi/6)=2 * sin(0) * cos(-pi/6):=
begin
have : sin(-pi/6) = -cos(433*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) + sin(pi/6) = 2 * sin(0) * cos(-pi/6),
{
rw sin_add_sin,
have : sin(((-pi/6) + (pi/6))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (pi/6))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_36_test : cos(147*pi)**2=1 - sin(pi) ** 2:=
begin
have : cos(pi) = cos(147*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) ** 2 = 1 - sin(pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_37_test : -cos(140*pi/3)=2 * cos(-pi/6) ** 2 - 1:=
begin
have : cos(-pi/3) = -cos(140*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = 2 * cos(-pi/6) ** 2 - 1,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_38_test (h0 : tan(247*pi/12)≠ 0) : -1/tan(247*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / tan(247 * pi / 12) = -1/tan(247*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(247*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_39_test : -sin(271*pi/6)=1 / 2:=
begin
have : cos(pi/3) = -sin(271*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end




lemma Trigo_41_test : -cos(199*pi)=- sin(223*pi/2):=
begin
have : sin(pi/2) = -cos(199*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(223*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_43_test : cos(48*pi)=cos(170*pi):=
begin
have : sin(pi/2) = cos(48*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(170*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_44_test : sin(-pi/6)*cos(-11*pi/6) + sin(-11*pi/6)*cos(-pi/6)=- sin(70*pi):=
begin
have : sin((-11) * pi / 6) * cos(-pi / 6) + sin(-pi / 6) * cos((-11) * pi / 6) = sin(-pi/6)*cos(-11*pi/6) + sin(-11*pi/6)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-11*pi/6) * cos(-pi/6) + sin(-pi/6) * cos(-11*pi/6),
{
have : sin(-2*pi) = sin((-11*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(70*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_45_test : sin(373*pi/3)=- cos(125*pi/6):=
begin
have : cos(pi/6) = sin(373*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(125*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_46_test : sin(5*pi/3)*cos(-pi/3) - sin(-pi/3)*cos(5*pi/3)=- sin(66*pi):=
begin
have : sin(2*pi) = sin(5*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(5*pi/3),
{
have : sin(2*pi) = sin((5*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(66*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_48_test : sin(-pi/6)=cos(202*pi/3):=
begin
have : cos(230*pi/3) = cos(202*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (230*pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = cos(230*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_49_test : 2*sin(-5*pi/6)*cos(-5*pi/6)=sin(-2*pi) * cos(pi/3) + sin(pi/3) * cos(-2*pi):=
begin
have : 2 * sin((-5) * pi / 6) * cos((-5) * pi / 6) = 2*sin(-5*pi/6)*cos(-5*pi/6),
{
field_simp at *,
},
have : sin(-5*pi/3) = 2 * sin(-5*pi/6) * cos(-5*pi/6),
{
have : sin(-5*pi/3) = sin(2*(-5*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/3) = sin(-2*pi) * cos(pi/3) + sin(pi/3) * cos(-2*pi),
{
have : sin(-5*pi/3) = sin((-2*pi) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_50_test : sin(83*pi/2)=- sin(161*pi/2):=
begin
have : sin(-pi/2) = sin(83*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(161*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_51_test : (sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))*cos(pi/2)=sin(pi/2) / 2 + sin(3*pi/2) / 2:=
begin
have : (sin(2 * pi) * cos(-pi) + sin(-pi) * cos(2 * pi)) * cos(pi / 2) = (sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(2*pi) * cos(-pi) + sin(-pi) * cos(2*pi),
{
have : sin(pi) = sin((2*pi) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(pi/2) = sin(pi/2) / 2 + sin(3*pi/2) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (pi/2)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/2)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_52_test : -sin(1721*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -sin(1721*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_53_test (h0 : cos(565*pi/3)≠ 0) : sin(-pi/3)/cos(565*pi/3)=tan(-pi/3):=
begin
have : cos(-pi/3) = cos(565*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_54_test (h0 : sin(97*pi/2)≠ 0) : sin(2*pi)/sin(97*pi/2)=tan(2*pi):=
begin
have : cos(2*pi) = sin(97*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) / cos(2*pi) = tan(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_55_test : sin(47*pi/2)**2=cos(2*pi) / 2 + 1 / 2:=
begin
have : cos(pi) = sin(47*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) ** 2 = cos(2*pi) / 2 + 1 / 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
rw this,
end




lemma Trigo_57_test (h0 : cos(-pi/2)≠ 0) (h1 : (4*cos(-pi/2)**2)≠ 0) (h2 : (2*cos(-pi/2))≠ 0) : cos(-pi)=-sin(-pi)**2/(4*cos(-pi/2)**2) + cos(-pi/2)**2:=
begin
have : -(sin(-pi) / (2 * cos(-pi / 2))) ** 2 + cos(-pi / 2) ** 2 = -sin(-pi)**2/(4*cos(-pi/2)**2) + cos(-pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = sin(-pi) / ( 2 * cos(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = - sin(-pi/2) ** 2 + cos(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end




lemma Trigo_59_test : -4*sin(pi/18)**3 + 3*sin(pi/18)=- sin(35*pi/6):=
begin
have : (-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18) = -4*sin(pi/18)**3 + 3*sin(pi/18),
{
field_simp at *,
},
have : sin(pi/6) = -4 * sin(pi/18) ** 3 + 3 * sin(pi/18),
{
have : sin(pi/6) = sin(3*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(35*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_60_test : -sin(pi/2)**2 + cos(pi/2)**2=- sin(97*pi/2):=
begin
have : cos(pi) = -sin(pi/2) ** 2 + cos(pi/2) ** 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - sin(97*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_61_test : -cos(427*pi/3)=1 - 2 * sin(-pi/3) ** 2:=
begin
have : cos(-2*pi/3) = -cos(427*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = 1 - 2 * sin(-pi/3) ** 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_62_test : sin(517*pi/6)=1 / 2:=
begin
have : sin(pi/6) = sin(517*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_63_test : cos(pi) - sin(311*pi/3)=2 * cos(-7*pi/12) * cos(5*pi/12):=
begin
have : -sin(311 * pi / 3) + cos(pi) = cos(pi) - sin(311*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(311*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) + cos(pi) = 2 * cos(-7*pi/12) * cos(5*pi/12),
{
rw cos_add_cos,
have : cos(((-pi/6) + (pi))/2) = cos(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (pi))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_64_test : cos(219*pi/2)=0:=
begin
have : cos(pi/2) = cos(219*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_65_test : sin(-pi/6) ** 2=1 - sin(193*pi/3)**2:=
begin
have : cos(-pi/6) = sin(193*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) ** 2 = 1 - cos(-pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end




lemma Trigo_67_test : -sin(166*pi)=0:=
begin
have : cos(pi/2) = -sin(166*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_68_test : cos(157*pi)=- 1:=
begin
have : cos(pi) = cos(157*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_69_test : cos(-pi/2)=-sin(306*pi):=
begin
have : sin(162*pi) = sin(306*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (162*pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(162*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_70_test : cos(509*pi/6)=- cos(1093*pi/6):=
begin
have : sin(-pi/3) = cos(509*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - cos(1093*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_71_test (h0 : tan(263*pi/4)≠ 0) : -1/tan(263*pi/4)=1:=
begin
have : (-1) / tan(263 * pi / 4) = -1/tan(263*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(263*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_72_test : -sin(136*pi)=cos(311*pi/2):=
begin
have : sin(-2*pi) = -sin(136*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(311*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_74_test : sin(-pi/2) ** 2=1 - sin(127*pi)**2:=
begin
have : cos(-pi/2) = sin(127*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) ** 2 = 1 - cos(-pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_75_test (h0 : cos((2*pi/3)/2)≠ 0) (h1 : (cos(2*pi/3)+1)≠ 0) (h2 : (1+cos(2*pi/3))≠ 0) : sin(2*pi/3)/(cos(2*pi/3) + 1)=tan(31*pi/3):=
begin
have : sin(2 * pi / 3) / (1 + cos(2 * pi / 3)) = sin(2*pi/3)/(cos(2*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sin(2*pi/3) / ( 1 + cos(2*pi/3) ),
{
have : tan(pi/3) = tan((2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(31*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_76_test (h0 : (1-2*sin(pi/6)**2)≠ 0) : sin(pi/3)/(1 - 2*sin(pi/6)**2)=tan(pi/3):=
begin
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_77_test : -cos(211*pi/2)=2 * sin(2*pi) * cos(2*pi):=
begin
have : sin(4*pi) = -cos(211*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi) = 2 * sin(2*pi) * cos(2*pi),
{
have : sin(4*pi) = sin(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_78_test : -cos(154*pi/3)=cos(131*pi/3):=
begin
have : cos(pi/3) = -cos(154*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(131*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_79_test : 1 - 2*sin(-3*pi/4)**2=- sin(-pi/2) * sin(-pi) + cos(-pi/2) * cos(-pi):=
begin
have : 1 - 2 * sin((-3) * pi / 4) ** 2 = 1 - 2*sin(-3*pi/4)**2,
{
field_simp at *,
},
have : cos(-3*pi/2) = 1 - 2 * sin(-3*pi/4) ** 2,
{
have : cos(-3*pi/2) = cos(2*(-3*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = - sin(-pi/2) * sin(-pi) + cos(-pi/2) * cos(-pi),
{
have : cos(-3*pi/2) = cos((-pi/2) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_80_test : sin(-pi/6)**2 + cos(305*pi/6)**2=1:=
begin
have : sin(-pi / 6) ** 2 + (-cos(305 * pi / 6)) ** 2 = sin(-pi/6)**2 + cos(305*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -cos(305*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) ** 2 + cos(-pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end






lemma Trigo_83_test : -sin(pi)**2 + cos(pi)**2 + cos(-2*pi)=2 * cos(2*pi) * cos(0):=
begin
have : -sin(pi) ** 2 + cos(pi) ** 2 + cos((-2) * pi) = -sin(pi)**2 + cos(pi)**2 + cos(-2*pi),
{
field_simp at *,
},
have : cos(2*pi) = -sin(pi) ** 2 + cos(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) + cos(-2*pi) = 2 * cos(2*pi) * cos(0),
{
rw cos_add_cos,
have : cos(((2*pi) + (-2*pi))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (-2*pi))/2) = cos(2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_85_test : -sin(56*pi)=4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6):=
begin
have : cos(-pi/2) = -sin(56*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6),
{
have : cos(-pi/2) = cos(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_86_test : tan(387*pi/4)=- 1:=
begin
have : tan(3*pi/4) = tan(387*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (3*pi/4) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_87_test : tan(115*pi/2)=1 / tan(26*pi):=
begin
have : tan(pi/2) = tan(115*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = 1 / tan(26*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/2) (26),
focus{repeat {apply congr_arg _}},
simp,
},
rw this,
end


lemma Trigo_88_test : -sin(538*pi/3)*cos(pi/3)=cos(-pi/6) / 2 + cos(pi/2) / 2:=
begin
have : cos(pi/6) = -sin(538*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) * cos(pi/3) = cos(-pi/6) / 2 + cos(pi/2) / 2,
{
rw cos_mul_cos,
have : cos((pi/6) + (pi/3)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (pi/3)) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_89_test : sin(665*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = sin(665*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi/6) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end




lemma Trigo_91_test : cos(-pi/2)=4*sin(160*pi/3)**3 - 3*sin(160*pi/3):=
begin
have : -((-4) * sin(160 * pi / 3) ** 3 + 3 * sin(160 * pi / 3)) = 4*sin(160*pi/3)**3 - 3*sin(160*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(160*pi) = -4 * sin(160*pi/3) ** 3 + 3 * sin(160*pi/3),
{
have : sin(160*pi) = sin(3*(160*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(160*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_94_test : sin(181*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(181*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end




lemma Trigo_96_test : sin(9*pi/2)=2 * cos(-pi) ** 2 - 1:=
begin
have : cos(-2*pi) = sin(9*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = 2 * cos(-pi) ** 2 - 1,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_97_test : cos(-pi/6) - cos(-2*pi)=-2*(sin(pi/3)*cos(7*pi/12) + sin(7*pi/12)*cos(pi/3))*sin(-13*pi/12):=
begin
have : (-2) * (sin(7 * pi / 12) * cos(pi / 3) + sin(pi / 3) * cos(7 * pi / 12)) * sin((-13) * pi / 12) = -2*(sin(pi/3)*cos(7*pi/12) + sin(7*pi/12)*cos(pi/3))*sin(-13*pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : sin(11*pi/12) = sin(7*pi/12) * cos(pi/3) + sin(pi/3) * cos(7*pi/12),
{
have : sin(11*pi/12) = sin((7*pi/12) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) - cos(-2*pi) = - 2 * sin(11*pi/12) * sin(-13*pi/12),
{
rw cos_sub_cos,
have : sin(((-pi/6) + (-2*pi))/2) = sin(-13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (-2*pi))/2) = sin(11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_98_test : sin(11*pi/6)*cos(-2*pi) + sin(-2*pi)*cos(11*pi/6)=cos(160*pi/3):=
begin
have : sin(11 * pi / 6) * cos((-2) * pi) + sin((-2) * pi) * cos(11 * pi / 6) = sin(11*pi/6)*cos(-2*pi) + sin(-2*pi)*cos(11*pi/6),
{
field_simp at *,
},
have : sin(-pi/6) = sin(11*pi/6) * cos(-2*pi) + sin(-2*pi) * cos(11*pi/6),
{
have : sin(-pi/6) = sin((11*pi/6) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(160*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_99_test : sin(217*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = sin(217*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_100_test : sin(-7*pi/3)*cos(-pi/3) - sin(-pi/3)*cos(-7*pi/3)=- sin(82*pi):=
begin
have : sin((-7) * pi / 3) * cos(-pi / 3) - sin(-pi / 3) * cos((-7) * pi / 3) = sin(-7*pi/3)*cos(-pi/3) - sin(-pi/3)*cos(-7*pi/3),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-7*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(-7*pi/3),
{
have : sin(-2*pi) = sin((-7*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(82*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_101_test : -sin(pi/6)**2 + cos(pi/6)**2=- cos(58*pi/3):=
begin
have : cos(pi/3) = -sin(pi/6) ** 2 + cos(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - cos(58*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_102_test : sin(217*pi/3)=- cos(713*pi/6):=
begin
have : cos(-pi/6) = sin(217*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(713*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_103_test : sin(655*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = sin(655*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_104_test : sin(pi/6) - sin(pi/2)=2*(1 - 2*sin(pi/6)**2)*sin(-pi/6):=
begin
have : 2 * sin(-pi / 6) * (1 - 2 * sin(pi / 6) ** 2) = 2*(1 - 2*sin(pi/6)**2)*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) - sin(pi/2) = 2 * sin(-pi/6) * cos(pi/3),
{
rw sin_sub_sin,
have : cos(((pi/6) + (pi/2))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (pi/2))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_105_test : sin(2*pi) * sin(pi/6)=-sin(-pi/6)*sin(2*pi):=
begin
have : 1 / 2 * ((-2) * sin(-pi / 6) * sin(2 * pi)) = -sin(-pi/6)*sin(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(11*pi/6) - cos(13*pi/6) = -2 * sin(-pi/6) * sin(2*pi),
{
rw cos_sub_cos,
have : sin(((11*pi/6) + (13*pi/6))/2) = sin(2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((11*pi/6) - (13*pi/6))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(11*pi/6) - cos(13*pi/6)) = cos(11*pi/6)/2-cos(13*pi/6)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(2*pi) * sin(pi/6) = cos(11*pi/6) / 2 - cos(13*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((2*pi) + (pi/6)) = cos(13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (pi/6)) = cos(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_106_test : cos(5*pi/6)=-2*sin(pi/4)*sin(pi/3)*cos(pi/4) + cos(pi/3)*cos(pi/2):=
begin
have : -sin(pi / 3) * (2 * sin(pi / 4) * cos(pi / 4)) + cos(pi / 3) * cos(pi / 2) = -2*sin(pi/4)*sin(pi/3)*cos(pi/4) + cos(pi/3)*cos(pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = 2 * sin(pi/4) * cos(pi/4),
{
have : sin(pi/2) = sin(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/6) = - sin(pi/3) * sin(pi/2) + cos(pi/3) * cos(pi/2),
{
have : cos(5*pi/6) = cos((pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_107_test : -cos(25*pi)=- sin(391*pi/2):=
begin
have : sin(pi/2) = -cos(25*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(391*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_108_test : -sin(-pi/2)*cos(314*pi/3)=sin(-5*pi/6) / 2 + sin(-pi/6) / 2:=
begin
have : sin(-pi / 2) * -cos(314 * pi / 3) = -sin(-pi/2)*cos(314*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(314*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(pi/3) = sin(-5*pi/6) / 2 + sin(-pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-pi/2) + (pi/3)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (pi/3)) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_109_test : -sin(508*pi/3)*cos(-pi)=cos(7*pi/6) / 2 + cos(-5*pi/6) / 2:=
begin
have : cos(pi/6) = -sin(508*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) * cos(-pi) = cos(7*pi/6) / 2 + cos(-5*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((pi/6) + (-pi)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (-pi)) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_110_test : 2*sin(pi/4)*cos(pi/4)=sin(pi/6) * cos(-pi/3) - sin(-pi/3) * cos(pi/6):=
begin
have : sin(pi/2) = 2 * sin(pi/4) * cos(pi/4),
{
have : sin(pi/2) = sin(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(pi/6) * cos(-pi/3) - sin(-pi/3) * cos(pi/6),
{
have : sin(pi/2) = sin((pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_111_test : (-1 + 2*cos(-pi/4)**2)*sin(pi)=- sin(-3*pi/2) / 2 + sin(pi/2) / 2:=
begin
have : sin(pi) * (2 * cos(-pi / 4) ** 2 - 1) = (-1 + 2*cos(-pi/4)**2)*sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 2 * cos(-pi/4) ** 2 - 1,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(-pi/2) = - sin(-3*pi/2) / 2 + sin(pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (pi)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (pi)) = sin(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_112_test : sin(-2*pi/3)=-sin(pi/2)*cos(-pi/6) + sin(-pi/6)*cos(391*pi/2):=
begin
have : sin(-pi / 6) * cos(391 * pi / 2) - sin(pi / 2) * cos(-pi / 6) = -sin(pi/2)*cos(-pi/6) + sin(-pi/6)*cos(391*pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = cos(391*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/3) = sin(-pi/6) * cos(pi/2) - sin(pi/2) * cos(-pi/6),
{
have : sin(-2*pi/3) = sin((-pi/6) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_113_test : sin(77*pi)=- sin(72*pi):=
begin
have : sin(2*pi) = sin(77*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(72*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_114_test : sin(-pi/2) ** 2=1 - cos(377*pi/2)**2:=
begin
have : cos(-pi/2) = cos(377*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) ** 2 = 1 - cos(-pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_115_test : -sin(215*pi/3)=- sin(418*pi/3):=
begin
have : sin(pi/3) = -sin(215*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(418*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_116_test : sin(325*pi/3)=- cos(847*pi/6):=
begin
have : cos(-pi/6) = sin(325*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(847*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_117_test : cos(257*pi/6)=sin(-pi) * sin(pi/6) + cos(-pi) * cos(pi/6):=
begin
have : cos(-7*pi/6) = cos(257*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-7*pi/6) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/6) = sin(-pi) * sin(pi/6) + cos(-pi) * cos(pi/6),
{
have : cos(-7*pi/6) = cos((-pi) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end




lemma Trigo_119_test : -sin(-pi/3)*sin(4*pi/3) + cos(-pi/3)*cos(4*pi/3)=- sin(2*pi) * sin(-pi) + cos(2*pi) * cos(-pi):=
begin
have : -sin(4 * pi / 3) * sin(-pi / 3) + cos(4 * pi / 3) * cos(-pi / 3) = -sin(-pi/3)*sin(4*pi/3) + cos(-pi/3)*cos(4*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(4*pi/3) * sin(-pi/3) + cos(4*pi/3) * cos(-pi/3),
{
have : cos(pi) = cos((4*pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - sin(2*pi) * sin(-pi) + cos(2*pi) * cos(-pi),
{
have : cos(pi) = cos((2*pi) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end






lemma Trigo_122_test : cos(-4*pi)=-1/2 + cos(-4*pi)/2 + cos(-2*pi)**2:=
begin
have : -(1 / 2 - cos((-4) * pi) / 2) + cos((-2) * pi) ** 2 = -1/2 + cos(-4*pi)/2 + cos(-2*pi)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) ** 2 = 1 / 2 - cos(-4*pi) / 2,
{
have : cos(-4*pi) = cos(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi) = - sin(-2*pi) ** 2 + cos(-2*pi) ** 2,
{
have : cos(-4*pi) = cos(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_123_test : -sin(581*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = -sin(581*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_124_test : sin(87*pi/2)=- cos(160*pi):=
begin
have : cos(pi) = sin(87*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(160*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_125_test : sin(275*pi/2)=cos(113*pi):=
begin
have : cos(pi) = sin(275*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(113*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_126_test : -sin(287*pi/2)=- cos(51*pi):=
begin
have : cos(2*pi) = -sin(287*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - cos(51*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_128_test (h0 : cos((pi/3)/2)≠ 0) (h1 : sin(pi/3)≠ 0) : (1 - cos(pi/3))/sin(pi/3)=- 1 / tan(17*pi/3):=
begin
have : tan(pi/6) = ( 1 - cos(pi/3) ) / sin(pi/3),
{
have : tan(pi/6) = tan((pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = - 1 / tan(17*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_130_test : -cos(335*pi/6)=sin(-pi/3) * cos(2*pi) - sin(2*pi) * cos(-pi/3):=
begin
have : sin(-7*pi/3) = -cos(335*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-7*pi/3) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/3) = sin(-pi/3) * cos(2*pi) - sin(2*pi) * cos(-pi/3),
{
have : sin(-7*pi/3) = sin((-pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_131_test : sin(209*pi/6)**2 + sin(-pi/3)**2=1:=
begin
have : sin(-pi / 3) ** 2 + sin(209 * pi / 6) ** 2 = sin(209*pi/6)**2 + sin(-pi/3)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(209*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) ** 2 + cos(-pi/3) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_132_test (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : sin(pi) / cos(pi)=(1 - cos(2*pi))/sin(2*pi):=
begin
have : tan(pi) = ( 1 - cos(2*pi) ) / sin(2*pi),
{
have : tan(pi) = tan((2*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(pi) / cos(pi) = tan(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_134_test : -sin(304*pi/3)=- cos(1171*pi/6):=
begin
have : cos(pi/6) = -sin(304*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(1171*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_136_test : -cos(382*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(382*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_137_test : (cos(-pi/2)*cos(5*pi/6) - sin(-pi/2)*sin(5*pi/6))**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : (-sin(5 * pi / 6) * sin(-pi / 2) + cos(5 * pi / 6) * cos(-pi / 2)) ** 2 = (cos(-pi/2)*cos(5*pi/6) - sin(-pi/2)*sin(5*pi/6))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(5*pi/6) * sin(-pi/2) + cos(5*pi/6) * cos(-pi/2),
{
have : cos(pi/3) = cos((5*pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) ** 2 = cos(2*pi/3) / 2 + 1 / 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_138_test : sin(205*pi/2)=- sin(171*pi/2):=
begin
have : sin(pi/2) = sin(205*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(171*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_140_test : (-4*sin(pi/3)**3 + 3*sin(pi/3))*sin(pi/6)=cos(-5*pi/6) / 2 - cos(7*pi/6) / 2:=
begin
have : sin(pi / 6) * ((-4) * sin(pi / 3) ** 3 + 3 * sin(pi / 3)) = (-4*sin(pi/3)**3 + 3*sin(pi/3))*sin(pi/6),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -4 * sin(pi/3) ** 3 + 3 * sin(pi/3),
{
have : sin(pi) = sin(3*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * sin(pi) = cos(-5*pi/6) / 2 - cos(7*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((pi/6) + (pi)) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (pi)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_141_test : -tan(97*pi/2)=- tan(85*pi/2):=
begin
have : tan(pi/2) = -tan(97*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - tan(85*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/2) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_142_test (h0 : cos(2*pi)≠ 0) : tan(2*pi)=(-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))/cos(2*pi):=
begin
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) / cos(2 * pi) = (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))/cos(2*pi),
{
field_simp at *,
},
have : sin(2*pi) = -4 * sin(2*pi/3) ** 3 + 3 * sin(2*pi/3),
{
have : sin(2*pi) = sin(3*(2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(2*pi) = sin(2*pi) / cos(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_144_test (h0 : sin(-pi/2)≠ 0) (h1 : (2*sin(-pi/2))≠ 0) : sin(-pi)/(2*sin(-pi/2)) + cos(pi/6)=2 * cos(pi/3) * cos(-pi/6):=
begin
have : cos(pi / 6) + sin(-pi) / (2 * sin(-pi / 2)) = sin(-pi)/(2*sin(-pi/2)) + cos(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(-pi) / ( 2 * sin(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) + cos(-pi/2) = 2 * cos(pi/3) * cos(-pi/6),
{
rw cos_add_cos,
have : cos(((pi/6) + (-pi/2))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/6) - (-pi/2))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_146_test : cos(625*pi/6)=sin(224*pi/3):=
begin
have : cos(-pi/6) = cos(625*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(224*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_147_test : sin(-pi/2)=cos(-119*pi):=
begin
have : - -cos((-119) * pi) = cos(-119*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(196*pi) = -cos(-119*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (196*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = - cos(196*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_148_test : sin(pi/3)=-1 + 2*cos(83*pi/12)**2:=
begin
have : 2 * cos(83 * pi / 12) ** 2 - 1 = -1 + 2*cos(83*pi/12)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(83*pi/6) = 2 * cos(83*pi/12) ** 2 - 1,
{
have : cos(83*pi/6) = cos(2*(83*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = cos(83*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_149_test : cos(-pi/3)*cos(5*pi/3) + sin(-pi/3)*sin(5*pi/3)=sin(141*pi/2):=
begin
have : sin(5 * pi / 3) * sin(-pi / 3) + cos(5 * pi / 3) * cos(-pi / 3) = cos(-pi/3)*cos(5*pi/3) + sin(-pi/3)*sin(5*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(5*pi/3) * sin(-pi/3) + cos(5*pi/3) * cos(-pi/3),
{
have : cos(2*pi) = cos((5*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(141*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_150_test : sin(269*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = sin(269*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_151_test : sin(57*pi)=sin(12*pi):=
begin
have : cos(pi/2) = sin(57*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(12*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_152_test : cos(pi/3) - cos(pi)=-2*(-4*sin(2*pi/9)**3 + 3*sin(2*pi/9))*sin(-pi/3):=
begin
have : (-2) * sin(-pi / 3) * ((-4) * sin(2 * pi / 9) ** 3 + 3 * sin(2 * pi / 9)) = -2*(-4*sin(2*pi/9)**3 + 3*sin(2*pi/9))*sin(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) = -4 * sin(2*pi/9) ** 3 + 3 * sin(2*pi/9),
{
have : sin(2*pi/3) = sin(3*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) - cos(pi) = - 2 * sin(-pi/3) * sin(2*pi/3),
{
rw cos_sub_cos,
have : sin(((pi/3) + (pi))/2) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (pi))/2) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_153_test : sin(-2*pi) * sin(pi/6)=cos(125*pi/6)/2 + cos(-13*pi/6)/2:=
begin
have : cos((-13) * pi / 6) / 2 - -cos(125 * pi / 6) / 2 = cos(125*pi/6)/2 + cos(-13*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-11*pi/6) = -cos(125*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-11*pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * sin(pi/6) = cos(-13*pi/6) / 2 - cos(-11*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((-2*pi) + (pi/6)) = cos(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/6)) = cos(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_154_test : -sin(-2*pi)*cos(-11*pi/6) - sin(-pi) + sin(-11*pi/6)*cos(-2*pi)=2 * sin(7*pi/12) * cos(-5*pi/12):=
begin
have : sin((-11) * pi / 6) * cos((-2) * pi) - sin((-2) * pi) * cos((-11) * pi / 6) - sin(-pi) = -sin(-2*pi)*cos(-11*pi/6) - sin(-pi) + sin(-11*pi/6)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-11*pi/6) * cos(-2*pi) - sin(-2*pi) * cos(-11*pi/6),
{
have : sin(pi/6) = sin((-11*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) - sin(-pi) = 2 * sin(7*pi/12) * cos(-5*pi/12),
{
rw sin_sub_sin,
have : cos(((pi/6) + (-pi))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (-pi))/2) = sin(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_156_test : 2*sin(-3*pi/2)*sin(-pi/2)=- 2 * sin(3*pi/2) * sin(-pi/2):=
begin
have : (-1) * ((-2) * sin((-3) * pi / 2) * sin(-pi / 2)) = 2*sin(-3*pi/2)*sin(-pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) - cos(pi) = -2 * sin(-3*pi/2) * sin(-pi/2),
{
rw cos_sub_cos,
have : sin(((-2*pi) + (pi))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-2*pi) - (pi))/2) = sin(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : -1*(cos(-2*pi) - cos(pi)) = cos(pi)-cos(-2*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi) - cos(-2*pi) = - 2 * sin(3*pi/2) * sin(-pi/2),
{
rw cos_sub_cos,
have : sin(((pi) + (-2*pi))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi) - (-2*pi))/2) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_157_test (h0 : cos((4*pi)/2)≠ 0) (h1 : sin(4*pi)≠ 0) : (1 - cos(4*pi))/sin(4*pi)=1 / tan(55*pi/2):=
begin
have : tan(2*pi) = ( 1 - cos(4*pi) ) / sin(4*pi),
{
have : tan(2*pi) = tan((4*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = 1 / tan(55*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_158_test (h0 : cos(5*pi/2)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (tan(2*pi)*tan(5*pi/2)+1)≠ 0) (h3 : (1+tan(5*pi/2)*tan(2*pi))≠ 0) : (-tan(2*pi) + tan(5*pi/2))/(tan(2*pi)*tan(5*pi/2) + 1)=- 1 / tan(37*pi):=
begin
have : (tan(5 * pi / 2) - tan(2 * pi)) / (1 + tan(5 * pi / 2) * tan(2 * pi)) = (-tan(2*pi) + tan(5*pi/2))/(tan(2*pi)*tan(5*pi/2) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = ( tan(5*pi/2) - tan(2*pi) ) / ( 1 + tan(5*pi/2) * tan(2*pi) ),
{
have : tan(pi/2) = tan((5*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - 1 / tan(37*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_159_test : cos(-pi)*cos(-pi/3) + sin(-pi)*sin(-pi/3)=- sin(-pi/2) * sin(-pi/6) + cos(-pi/2) * cos(-pi/6):=
begin
have : sin(-pi) * sin(-pi / 3) + cos(-pi) * cos(-pi / 3) = cos(-pi)*cos(-pi/3) + sin(-pi)*sin(-pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = sin(-pi) * sin(-pi/3) + cos(-pi) * cos(-pi/3),
{
have : cos(-2*pi/3) = cos((-pi) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = - sin(-pi/2) * sin(-pi/6) + cos(-pi/2) * cos(-pi/6),
{
have : cos(-2*pi/3) = cos((-pi/2) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_160_test : cos(151*pi/6)**2=1 / 2 - cos(-2*pi/3) / 2:=
begin
have : sin(-pi/3) = cos(151*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) ** 2 = 1 / 2 - cos(-2*pi/3) / 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end






lemma Trigo_163_test : cos(527*pi/3) + cos(-pi/6)=2 * cos(pi/12) * cos(-pi/4):=
begin
have : cos(-pi / 6) + cos(527 * pi / 3) = cos(527*pi/3) + cos(-pi/6),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(527*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) + cos(-pi/3) = 2 * cos(pi/12) * cos(-pi/4),
{
rw cos_add_cos,
have : cos(((-pi/6) + (-pi/3))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (-pi/3))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_165_test (h0 : tan(152*pi/3)≠ 0) : -1/tan(152*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(152 * pi / 3) = -1/tan(152*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(152*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_166_test : sin(103*pi)=cos(193*pi/2):=
begin
have : sin(pi) = sin(103*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(193*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_167_test : sin(pi)=-cos(613*pi/2):=
begin
have : cos(323*pi/2) = -cos(613*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (323*pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = cos(323*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_169_test (h0 : sin(pi/2)≠ 0) : sin(108*pi)=sin(pi) / ( 2 * sin(pi/2) ):=
begin
have : cos(pi/2) = sin(108*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(pi) / ( 2 * sin(pi/2) ),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
rw this,
end


lemma Trigo_170_test : sin(-pi/3)=-sin(224*pi/3):=
begin
have : cos(19*pi/6) = -sin(224*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (19*pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = cos(19*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_171_test : (-sin(pi/12)**2 + cos(pi/12)**2)*cos(-pi/2)=cos(-2*pi/3) / 2 + cos(-pi/3) / 2:=
begin
have : cos(-pi / 2) * (-sin(pi / 12) ** 2 + cos(pi / 12) ** 2) = (-sin(pi/12)**2 + cos(pi/12)**2)*cos(-pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(pi/12) ** 2 + cos(pi/12) ** 2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) * cos(pi/6) = cos(-2*pi/3) / 2 + cos(-pi/3) / 2,
{
rw cos_mul_cos,
have : cos((-pi/2) + (pi/6)) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (pi/6)) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_172_test : cos(2*pi)=sin(405*pi/2):=
begin
have : sin(129*pi/2) = sin(405*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (129*pi/2) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(129*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_173_test : -sin(pi/4)**2 + cos(pi/4)**2=- cos(23*pi/2):=
begin
have : cos(pi/2) = -sin(pi/4) ** 2 + cos(pi/4) ** 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(23*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_174_test : -tan(61*pi)=- tan(62*pi):=
begin
have : tan(pi) = -tan(61*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - tan(62*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_175_test : sin(997*pi/6)=sin(1129*pi/6):=
begin
have : sin(pi/6) = sin(997*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(1129*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_176_test : sin(-pi) - sin(-pi/6)=2*(cos(17*pi/12)*cos(2*pi) + sin(17*pi/12)*sin(2*pi))*sin(-5*pi/12):=
begin
have : 2 * sin((-5) * pi / 12) * (sin(17 * pi / 12) * sin(2 * pi) + cos(17 * pi / 12) * cos(2 * pi)) = 2*(cos(17*pi/12)*cos(2*pi) + sin(17*pi/12)*sin(2*pi))*sin(-5*pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-7*pi/12) = sin(17*pi/12) * sin(2*pi) + cos(17*pi/12) * cos(2*pi),
{
have : cos(-7*pi/12) = cos((17*pi/12) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) - sin(-pi/6) = 2 * sin(-5*pi/12) * cos(-7*pi/12),
{
rw sin_sub_sin,
have : cos(((-pi) + (-pi/6))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (-pi/6))/2) = sin(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_177_test (h0 : cos((pi)/2)≠ 0) (h1 : sin(pi)≠ 0) : (1 - cos(pi))/sin(pi)=sin(pi/2) / cos(pi/2):=
begin
have : tan(pi/2) = ( 1 - cos(pi) ) / sin(pi),
{
have : tan(pi/2) = tan((pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = sin(pi/2) / cos(pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_178_test : tan(41*pi)=0:=
begin
have : tan(pi) = tan(41*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_179_test (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : (1 - cos(2*pi))/sin(2*pi)=sin(pi) / cos(pi):=
begin
have : tan(pi) = ( 1 - cos(2*pi) ) / sin(2*pi),
{
have : tan(pi) = tan((2*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_180_test : 2*cos(-5*pi/4)*cos(-3*pi/4)=2 * cos(5*pi/4) * cos(-3*pi/4):=
begin
have : 2 * cos((-5) * pi / 4) * cos((-3) * pi / 4) = 2*cos(-5*pi/4)*cos(-3*pi/4),
{
field_simp at *,
},
have : cos(-2*pi) + cos(pi/2) = 2 * cos(-5*pi/4) * cos(-3*pi/4),
{
rw cos_add_cos,
have : cos(((-2*pi) + (pi/2))/2) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi/2))/2) = cos(-5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(-2*pi) + cos(pi/2)) = cos(pi/2)+cos(-2*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi/2) + cos(-2*pi) = 2 * cos(5*pi/4) * cos(-3*pi/4),
{
rw cos_add_cos,
have : cos(((pi/2) + (-2*pi))/2) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/2) - (-2*pi))/2) = cos(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_181_test : sin(603*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = sin(603*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_182_test (h0 : tan(73*pi/2)≠ 0) : 1/tan(73*pi/2)=- tan(76*pi):=
begin
have : tan(pi) = 1 / tan(73*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - tan(76*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_183_test : sin(-pi)=1 - 2*sin(145*pi/4)**2:=
begin
have : cos(145*pi/2) = 1 - 2 * sin(145*pi/4) ** 2,
{
have : cos(145*pi/2) = cos(2*(145*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(145*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_184_test : -sin(-pi)*sin(4*pi/3) + cos(-pi)*cos(4*pi/3)=1 / 2:=
begin
have : -sin(4 * pi / 3) * sin(-pi) + cos(4 * pi / 3) * cos(-pi) = -sin(-pi)*sin(4*pi/3) + cos(-pi)*cos(4*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(4*pi/3) * sin(-pi) + cos(4*pi/3) * cos(-pi),
{
have : cos(pi/3) = cos((4*pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_185_test : sin(pi) - sin(-2*pi)=-sin(-2*pi) + sin(pi):=
begin
have : 2 * (-sin((-2) * pi) / 2 + sin(pi) / 2) = -sin(-2*pi) + sin(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi/2) * cos(-pi/2) = -sin(-2*pi) / 2 + sin(pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (3*pi/2)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (3*pi/2)) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(3*pi/2) * cos(-pi/2)) = 2*sin(3*pi/2)*cos(-pi/2),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi) - sin(-2*pi) = 2 * sin(3*pi/2) * cos(-pi/2),
{
rw sin_sub_sin,
have : cos(((pi) + (-2*pi))/2) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi) - (-2*pi))/2) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_186_test (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : sin(pi/3)/(2*cos(pi/6))=sin(-pi/3) * cos(-pi/2) - sin(-pi/2) * cos(-pi/3):=
begin
have : sin(pi/6) = sin(pi/3) / ( 2 * cos(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-pi/3) * cos(-pi/2) - sin(-pi/2) * cos(-pi/3),
{
have : sin(pi/6) = sin((-pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_187_test : -sin(471*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = -sin(471*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_188_test : cos(323*pi/3)**2 + cos(-pi/6)**2=1:=
begin
have : (-cos(323 * pi / 3)) ** 2 + cos(-pi / 6) ** 2 = cos(323*pi/3)**2 + cos(-pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(323*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) ** 2 + cos(-pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_189_test : sin(pi/3) * sin(-2*pi)=sin(-2*pi)*sin(pi/3):=
begin
have : (-1) / 2 * ((-2) * sin((-2) * pi) * sin(pi / 3)) = sin(-2*pi)*sin(pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/3) - cos(7*pi/3) = -2 * sin(-2*pi) * sin(pi/3),
{
rw cos_sub_cos,
have : sin(((-5*pi/3) + (7*pi/3))/2) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-5*pi/3) - (7*pi/3))/2) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : -1/2*(cos(-5*pi/3) - cos(7*pi/3)) = cos(7*pi/3)/2-cos(-5*pi/3)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/3) * sin(-2*pi) = cos(7*pi/3) / 2 - cos(-5*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((pi/3) + (-2*pi)) = cos(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (-2*pi)) = cos(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_191_test : sin(43*pi/2)**2=1 - cos(-pi/2) ** 2:=
begin
have : sin(-pi/2) = sin(43*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) ** 2 = 1 - cos(-pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end




lemma Trigo_193_test : sin(199*pi/2)=- sin(265*pi/2):=
begin
have : sin(-pi/2) = sin(199*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(265*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_194_test : -cos(119*pi)=sin(-pi/2) * cos(pi) + sin(pi) * cos(-pi/2):=
begin
have : sin(pi/2) = -cos(119*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(-pi/2) * cos(pi) + sin(pi) * cos(-pi/2),
{
have : sin(pi/2) = sin((-pi/2) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_195_test : -sin(-pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi/2)=sin(238*pi/3):=
begin
have : sin((-5) * pi / 6) * cos(-pi / 2) - sin(-pi / 2) * cos((-5) * pi / 6) = -sin(-pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-5*pi/6) * cos(-pi/2) - sin(-pi/2) * cos(-5*pi/6),
{
have : sin(-pi/3) = sin((-5*pi/6) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(238*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_196_test (h0 : cos(-pi/3)≠ 0) : tan(-pi/3)=(-sin(pi/2)*cos(pi/6) + sin(pi/6)*cos(pi/2))/cos(-pi/3):=
begin
have : (sin(pi / 6) * cos(pi / 2) - sin(pi / 2) * cos(pi / 6)) / cos(-pi / 3) = (-sin(pi/2)*cos(pi/6) + sin(pi/6)*cos(pi/2))/cos(-pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = sin(pi/6) * cos(pi/2) - sin(pi/2) * cos(pi/6),
{
have : sin(-pi/3) = sin((pi/6) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/3) = sin(-pi/3) / cos(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_197_test : -sin(114*pi)*cos(-pi)=cos(-pi/2) / 2 + cos(-3*pi/2) / 2:=
begin
have : cos(-pi) * -sin(114 * pi) = -sin(114*pi)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(114*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(-pi/2) = cos(-pi/2) / 2 + cos(-3*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (-pi/2)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-pi/2)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_198_test : cos(pi)/2 + cos(3*pi)/2=cos(-pi) / 2 + cos(3*pi) / 2:=
begin
have : cos(2*pi) * cos(pi) = cos(pi) / 2 + cos(3*pi) / 2,
{
rw cos_mul_cos,
have : cos((2*pi) + (pi)) = cos(3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (pi)) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(2*pi) * cos(pi)) = cos(pi)*cos(2*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi) * cos(2*pi) = cos(-pi) / 2 + cos(3*pi) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (2*pi)) = cos(3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (2*pi)) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_199_test : -cos(141*pi/2)=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : cos(pi/2) = -cos(141*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 4 * cos(pi/6) ** 3 - 3 * cos(pi/6),
{
have : cos(pi/2) = cos(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_200_test : -sin(-2*pi)*sin(7*pi/3) + cos(-2*pi)*cos(7*pi/3)=sin(pi/2) * sin(pi/6) + cos(pi/2) * cos(pi/6):=
begin
have : -sin(7 * pi / 3) * sin((-2) * pi) + cos(7 * pi / 3) * cos((-2) * pi) = -sin(-2*pi)*sin(7*pi/3) + cos(-2*pi)*cos(7*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(7*pi/3) * sin(-2*pi) + cos(7*pi/3) * cos(-2*pi),
{
have : cos(pi/3) = cos((7*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(pi/2) * sin(pi/6) + cos(pi/2) * cos(pi/6),
{
have : cos(pi/3) = cos((pi/2) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_201_test : cos(434*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(434*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end






lemma Trigo_204_test : cos(pi/3)=-1 + 2*cos(pi/6)**2:=
begin
have : 1 - 2 * (1 - cos(pi / 6) ** 2) = -1 + 2*cos(pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 - cos(pi/6) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_205_test : cos(52*pi)=cos(136*pi):=
begin
have : cos(-2*pi) = cos(52*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(136*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_206_test : sin(pi/6)=-cos(-pi/2)*cos(1057*pi/6) - sin(-pi/2)*sin(1057*pi/6):=
begin
have : -(sin(1057 * pi / 6) * sin(-pi / 2) + cos(1057 * pi / 6) * cos(-pi / 2)) = -cos(-pi/2)*cos(1057*pi/6) - sin(-pi/2)*sin(1057*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(530*pi/3) = sin(1057*pi/6) * sin(-pi/2) + cos(1057*pi/6) * cos(-pi/2),
{
have : cos(530*pi/3) = cos((1057*pi/6) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(530*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end








lemma Trigo_210_test : -cos(877*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(877*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_211_test : -cos(47*pi/2)=- cos(199*pi/2):=
begin
have : sin(2*pi) = -cos(47*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(199*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_212_test : cos(103*pi/2)**2=cos(pi) / 2 + 1 / 2:=
begin
have : cos(pi/2) = cos(103*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) ** 2 = cos(pi) / 2 + 1 / 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_213_test : cos(2371*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = cos(2371*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_214_test : sin(-pi/6) * cos(-pi)=sin(-pi/6)*cos(pi):=
begin
have : 1 / 2 * (2 * sin(-pi / 6) * cos(pi)) = sin(-pi/6)*cos(pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/6) + sin(-7*pi/6) = 2 * sin(-pi/6) * cos(pi),
{
rw sin_add_sin,
have : sin(((5*pi/6) + (-7*pi/6))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((5*pi/6) - (-7*pi/6))/2) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 1/2*(sin(5*pi/6) + sin(-7*pi/6)) = sin(5*pi/6)/2+sin(-7*pi/6)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi/6) * cos(-pi) = sin(5*pi/6) / 2 + sin(-7*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-pi/6) + (-pi)) = sin(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (-pi)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_215_test : cos(pi/2)=cos(-13*pi/2):=
begin
have : cos((-13) * pi / 2) = cos(-13*pi/2),
{
field_simp at *,
},
have : sin(13*pi) = cos(-13*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (13*pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(13*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_216_test : -sin(235*pi/6)=- cos(284*pi/3):=
begin
have : sin(pi/6) = -sin(235*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - cos(284*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_217_test (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : sin(pi)/(2*sin(pi/2))=- cos(243*pi/2):=
begin
have : cos(pi/2) = sin(pi) / ( 2 * sin(pi/2) ),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(243*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_218_test : sin(129*pi/2)=1 - 2 * sin(-2*pi) ** 2:=
begin
have : cos(-4*pi) = sin(129*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-4*pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-4*pi) = 1 - 2 * sin(-2*pi) ** 2,
{
have : cos(-4*pi) = cos(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_219_test (h0 : cos((-2*pi)/2)≠ 0) (h1 : (1+cos(-2*pi))≠ 0) (h2 : (1+cos((-2)*pi))≠ 0) : sin(-2*pi)/(1 + cos(-2*pi))=tan(96*pi):=
begin
have : sin((-2) * pi) / (1 + cos((-2) * pi)) = sin(-2*pi)/(1 + cos(-2*pi)),
{
field_simp at *,
},
have : tan(-pi) = sin(-2*pi) / ( 1 + cos(-2*pi) ),
{
have : tan(-pi) = tan((-2*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(96*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_221_test : cos(533*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = cos(533*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_222_test : (-sin(-2*pi/3)*sin(pi) + cos(-2*pi/3)*cos(pi))**2 + sin(pi/3)**2=1:=
begin
have : sin(pi / 3) ** 2 + (-sin((-2) * pi / 3) * sin(pi) + cos((-2) * pi / 3) * cos(pi)) ** 2 = (-sin(-2*pi/3)*sin(pi) + cos(-2*pi/3)*cos(pi))**2 + sin(pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(-2*pi/3) * sin(pi) + cos(-2*pi/3) * cos(pi),
{
have : cos(pi/3) = cos((-2*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 + cos(pi/3) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_223_test : -sin(pi) - cos(598*pi/3)=2 * sin(-5*pi/12) * cos(7*pi/12):=
begin
have : -cos(598 * pi / 3) - sin(pi) = -sin(pi) - cos(598*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(598*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) - sin(pi) = 2 * sin(-5*pi/12) * cos(7*pi/12),
{
rw sin_sub_sin,
have : cos(((pi/6) + (pi))/2) = cos(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (pi))/2) = sin(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_224_test : sin(2*pi/3)=sin(pi)*cos(-pi/3) - sin(-pi/3)*cos(150*pi):=
begin
have : sin(pi) * cos(-pi / 3) + sin(-pi / 3) * -cos(150 * pi) = sin(pi)*cos(-pi/3) - sin(-pi/3)*cos(150*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -cos(150*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) = sin(pi) * cos(-pi/3) + sin(-pi/3) * cos(pi),
{
have : sin(2*pi/3) = sin((pi) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_225_test : cos(263*pi/2)=0:=
begin
have : sin(pi) = cos(263*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end




lemma Trigo_227_test : sin(3*pi/2)=sin(-pi/2)*cos(2*pi) + sin(2*pi)*cos(217*pi/2):=
begin
have : sin(2 * pi) * cos(217 * pi / 2) + sin(-pi / 2) * cos(2 * pi) = sin(-pi/2)*cos(2*pi) + sin(2*pi)*cos(217*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = cos(217*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi/2) = sin(2*pi) * cos(-pi/2) + sin(-pi/2) * cos(2*pi),
{
have : sin(3*pi/2) = sin((2*pi) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_228_test : -cos(605*pi/6)=- cos(1169*pi/6):=
begin
have : cos(pi/6) = -cos(605*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(1169*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_229_test (h0 : (4*cos(-pi/6)**3-3*cos(-pi/6))≠ 0) (h1 : (-3*cos(-pi/6)+4*cos(-pi/6)**3)≠ 0) : sin(-pi/2)/(-3*cos(-pi/6) + 4*cos(-pi/6)**3)=tan(-pi/2):=
begin
have : sin(-pi / 2) / (4 * cos(-pi / 6) ** 3 - 3 * cos(-pi / 6)) = sin(-pi/2)/(-3*cos(-pi/6) + 4*cos(-pi/6)**3),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6),
{
have : cos(-pi/2) = cos(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) / cos(-pi/2) = tan(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_230_test : -1 + 2*cos(-pi/6)**2=- cos(364*pi/3):=
begin
have : 2 * cos(-pi / 6) ** 2 - 1 = -1 + 2*cos(-pi/6)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = 2 * cos(-pi/6) ** 2 - 1,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(364*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_231_test : sin(pi/6)*cos(pi/3) + sin(pi/3)*cos(pi/6)=- sin(131*pi/2):=
begin
have : sin(pi/2) = sin(pi/6) * cos(pi/3) + sin(pi/3) * cos(pi/6),
{
have : sin(pi/2) = sin((pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(131*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_232_test : 2*sin(-pi/12)*cos(-pi/12)=- sin(625*pi/6):=
begin
have : sin(-pi/6) = 2 * sin(-pi/12) * cos(-pi/12),
{
have : sin(-pi/6) = sin(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(625*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_233_test : cos(93*pi/2)=2 * sin(-2*pi) * cos(-2*pi):=
begin
have : sin(-4*pi) = cos(93*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-4*pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-4*pi) = 2 * sin(-2*pi) * cos(-2*pi),
{
have : sin(-4*pi) = sin(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_234_test (h0 : cos(-pi/2)≠ 0) (h1 : (1-tan(-pi/2)**2)≠ 0) : 2*tan(-pi/2)/(1 - tan(-pi/2)**2)=- tan(40*pi):=
begin
have : tan(-pi) = 2 * tan(-pi/2) / ( 1 - tan(-pi/2) ** 2 ),
{
have : tan(-pi) = tan(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - tan(40*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_236_test (h0 : cos(0)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (tan(0)*tan(-pi/3)+1)≠ 0) (h3 : (1+tan(0)*tan(-pi/3))≠ 0) : (tan(0) - tan(-pi/3))/(tan(0)*tan(-pi/3) + 1)=sqrt( 3 ):=
begin
have : (tan(0) - tan(-pi / 3)) / (1 + tan(0) * tan(-pi / 3)) = (tan(0) - tan(-pi/3))/(tan(0)*tan(-pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( tan(0) - tan(-pi/3) ) / ( 1 + tan(0) * tan(-pi/3) ),
{
have : tan(pi/3) = tan((0) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_237_test : cos(2*pi)=-cos(33*pi):=
begin
have : sin(217*pi/2) = -cos(33*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (217*pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(217*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_239_test : -sin(-11*pi/6)*sin(2*pi) + cos(-11*pi/6)*cos(2*pi)=cos(1009*pi/6):=
begin
have : -sin((-11) * pi / 6) * sin(2 * pi) + cos((-11) * pi / 6) * cos(2 * pi) = -sin(-11*pi/6)*sin(2*pi) + cos(-11*pi/6)*cos(2*pi),
{
field_simp at *,
},
have : cos(pi/6) = -sin(-11*pi/6) * sin(2*pi) + cos(-11*pi/6) * cos(2*pi),
{
have : cos(pi/6) = cos((-11*pi/6) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(1009*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_240_test : sin(2*pi)=-cos(259*pi/2):=
begin
have : cos(35*pi/2) = -cos(259*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (35*pi/2) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = cos(35*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_241_test : sin(-2*pi)=sin(124*pi):=
begin
have : - -sin(124 * pi) = sin(124*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -sin(124*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = - cos(pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (1),
focus{repeat {apply congr_arg _}},
simp,
},
rw this,
end


lemma Trigo_242_test : cos(141*pi)=- cos(30*pi):=
begin
have : cos(pi) = cos(141*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(30*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_243_test : tan(289*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = tan(289*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_244_test : cos(2*pi)=-4*sin(5*pi/6)**3 + 3*sin(5*pi/6):=
begin
have : (-4) * sin(5 * pi / 6) ** 3 + 3 * sin(5 * pi / 6) = -4*sin(5*pi/6)**3 + 3*sin(5*pi/6),
{
field_simp at *,
},
have : sin(5*pi/2) = -4 * sin(5*pi/6) ** 3 + 3 * sin(5*pi/6),
{
have : sin(5*pi/2) = sin(3*(5*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(5*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_245_test : sin(2*pi)=1 - 2*cos(357*pi/4)**2:=
begin
have : -(2 * cos(357 * pi / 4) ** 2 - 1) = 1 - 2*cos(357*pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(357*pi/2) = 2 * cos(357*pi/4) ** 2 - 1,
{
have : cos(357*pi/2) = cos(2*(357*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = - cos(357*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_246_test : sin(pi/2) + sin(2*pi)=2*sin(5*pi/4)*cos(659*pi/4):=
begin
have : cos(-3*pi/4) = cos(659*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-3*pi/4) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) + sin(2*pi) = 2 * sin(5*pi/4) * cos(-3*pi/4),
{
rw sin_add_sin,
have : sin(((pi/2) + (2*pi))/2) = sin(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/2) - (2*pi))/2) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end






lemma Trigo_249_test : cos(137*pi) + cos(pi/6)=2 * cos(-7*pi/12) * cos(-5*pi/12):=
begin
have : cos(-pi) = cos(137*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) + cos(pi/6) = 2 * cos(-7*pi/12) * cos(-5*pi/12),
{
rw cos_add_cos,
have : cos(((-pi) + (pi/6))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (pi/6))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_250_test : sin(230*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(230*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end




lemma Trigo_252_test : -cos(194*pi)=4 * cos(-pi/3) ** 3 - 3 * cos(-pi/3):=
begin
have : cos(-pi) = -cos(194*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = 4 * cos(-pi/3) ** 3 - 3 * cos(-pi/3),
{
have : cos(-pi) = cos(3*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_253_test : -sin(pi/4)**2 + cos(pi/4)**2=- sin(pi/3) * sin(pi/6) + cos(pi/3) * cos(pi/6):=
begin
have : cos(pi/2) = -sin(pi/4) ** 2 + cos(pi/4) ** 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - sin(pi/3) * sin(pi/6) + cos(pi/3) * cos(pi/6),
{
have : cos(pi/2) = cos((pi/3) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end






lemma Trigo_256_test : -cos(317*pi/6)=- cos(835*pi/6):=
begin
have : cos(-pi/6) = -cos(317*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(835*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_257_test : sin(-5*pi/2)*cos(-2*pi) - sin(-2*pi)*cos(-5*pi/2)=sin(243*pi/2):=
begin
have : sin((-5) * pi / 2) * cos((-2) * pi) - sin((-2) * pi) * cos((-5) * pi / 2) = sin(-5*pi/2)*cos(-2*pi) - sin(-2*pi)*cos(-5*pi/2),
{
field_simp at *,
},
have : sin(-pi/2) = sin(-5*pi/2) * cos(-2*pi) - sin(-2*pi) * cos(-5*pi/2),
{
have : sin(-pi/2) = sin((-5*pi/2) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(243*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_258_test (h0 : cos(-11*pi/6)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (tan(-2*pi)*tan(-11*pi/6)+1)≠ 0) (h3 : (1+tan((-11)*pi/6)*tan((-2)*pi))≠ 0) : (-tan(-2*pi) + tan(-11*pi/6))/(tan(-2*pi)*tan(-11*pi/6) + 1)=- 1 / tan(152*pi/3):=
begin
have : (tan((-11) * pi / 6) - tan((-2) * pi)) / (1 + tan((-11) * pi / 6) * tan((-2) * pi)) = (-tan(-2*pi) + tan(-11*pi/6))/(tan(-2*pi)*tan(-11*pi/6) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(-11*pi/6) - tan(-2*pi) ) / ( 1 + tan(-11*pi/6) * tan(-2*pi) ),
{
have : tan(pi/6) = tan((-11*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = - 1 / tan(152*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_260_test : -sin(86*pi)=sin(160*pi):=
begin
have : sin(-2*pi) = -sin(86*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(160*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_261_test : 2*sin(-pi)*cos(-pi)*cos(-pi/2)=sin(-3*pi/2) / 2 + sin(-5*pi/2) / 2:=
begin
have : sin(-2*pi) = 2 * sin(-pi) * cos(-pi),
{
have : sin(-2*pi) = sin(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/2) = sin(-3*pi/2) / 2 + sin(-5*pi/2) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-pi/2)) = sin(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-pi/2)) = sin(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_262_test : 2*sin(pi)*cos(pi)=- sin(115*pi):=
begin
have : sin(2*pi) = 2 * sin(pi) * cos(pi),
{
have : sin(2*pi) = sin(2*(pi)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(115*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_263_test (h0 : cos((pi/3)/2)≠ 0) (h1 : (cos(pi/3)+1)≠ 0) (h2 : (1+cos(pi/3))≠ 0) : sin(pi/3)/(cos(pi/3) + 1)=tan(7*pi/6):=
begin
have : sin(pi / 3) / (1 + cos(pi / 3)) = sin(pi/3)/(cos(pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sin(pi/3) / ( 1 + cos(pi/3) ),
{
have : tan(pi/6) = tan((pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(7*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_264_test : cos(-2*pi) ** 2=1 - cos(179*pi/2)**2:=
begin
have : sin(-2*pi) = cos(179*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) ** 2 = 1 - sin(-2*pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_265_test (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : sin(pi)/(2*sin(pi/2))=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : cos(pi/2) = sin(pi) / ( 2 * sin(pi/2) ),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 4 * cos(pi/6) ** 3 - 3 * cos(pi/6),
{
have : cos(pi/2) = cos(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_266_test : -cos(8*pi/3)=1 - 2 * sin(-pi/6) ** 2:=
begin
have : cos(-pi/3) = -cos(8*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = 1 - 2 * sin(-pi/6) ** 2,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_267_test : 1 - 2*sin(-pi/2)**2=cos(93*pi):=
begin
have : cos(-pi) = 1 - 2 * sin(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(93*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_268_test : 3*sin(-pi/9) - 4*sin(-pi/9)**3=- sin(260*pi/3):=
begin
have : (-4) * sin(-pi / 9) ** 3 + 3 * sin(-pi / 9) = 3*sin(-pi/9) - 4*sin(-pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -4 * sin(-pi/9) ** 3 + 3 * sin(-pi/9),
{
have : sin(-pi/3) = sin(3*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(260*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_270_test : sin(757*pi/6)=- cos(98*pi/3):=
begin
have : cos(-pi/3) = sin(757*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(98*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_271_test : -cos(929*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -cos(929*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_272_test : -cos(158*pi)=- 1:=
begin
have : cos(pi) = -cos(158*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_273_test : -sin(259*pi/6)=1 / 2:=
begin
have : cos(pi/3) = -sin(259*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_274_test : cos(110*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(110*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end




lemma Trigo_276_test : sin(2*pi) * cos(pi/6)=-sin(-2*pi)*cos(pi/6):=
begin
have : (-1) / 2 * (2 * sin((-2) * pi) * cos(pi / 6)) = -sin(-2*pi)*cos(pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-11*pi/6) - sin(13*pi/6) = 2 * sin(-2*pi) * cos(pi/6),
{
rw sin_sub_sin,
have : cos(((-11*pi/6) + (13*pi/6))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-11*pi/6) - (13*pi/6))/2) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -1/2*(sin(-11*pi/6) - sin(13*pi/6)) = -sin(-11*pi/6)/2+sin(13*pi/6)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(2*pi) * cos(pi/6) = - sin(-11*pi/6) / 2 + sin(13*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/6) + (2*pi)) = sin(13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (2*pi)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_277_test : tan(14*pi)=- 1 / tan(39*pi/2):=
begin
have : tan(-pi) = tan(14*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - 1 / tan(39*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_278_test (h0 : tan(80*pi/3)≠ 0) : -1/tan(80*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(80 * pi / 3) = -1/tan(80*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(80*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_279_test : -cos(9*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -cos(9*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_280_test : (-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(pi/6)=sin(pi/2) / 2 + sin(-pi/6) / 2:=
begin
have : sin(pi / 6) * (-sin(-pi / 6) ** 2 + cos(-pi / 6) ** 2) = (-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(-pi/6) ** 2 + cos(-pi/6) ** 2,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(-pi/3) = sin(pi/2) / 2 + sin(-pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/6) + (-pi/3)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (-pi/3)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_281_test : -sin(pi)*cos(7*pi/6) + sin(7*pi/6)*cos(pi)=sin(-pi/6) * cos(-pi/3) - sin(-pi/3) * cos(-pi/6):=
begin
have : sin(7 * pi / 6) * cos(pi) - sin(pi) * cos(7 * pi / 6) = -sin(pi)*cos(7*pi/6) + sin(7*pi/6)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(7*pi/6) * cos(pi) - sin(pi) * cos(7*pi/6),
{
have : sin(pi/6) = sin((7*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-pi/6) * cos(-pi/3) - sin(-pi/3) * cos(-pi/6),
{
have : sin(pi/6) = sin((-pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_282_test (h0 : tan(199*pi/4)≠ 0) : -1/tan(199*pi/4)=1:=
begin
have : (-1) / tan(199 * pi / 4) = -1/tan(199*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(199*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_283_test : sin(191*pi/2)=sin(-2*pi) * cos(pi/2) - sin(pi/2) * cos(-2*pi):=
begin
have : sin(-5*pi/2) = sin(191*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-5*pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/2) = sin(-2*pi) * cos(pi/2) - sin(pi/2) * cos(-2*pi),
{
have : sin(-5*pi/2) = sin((-2*pi) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_284_test : -cos(229*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -cos(229*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end










lemma Trigo_289_test : -cos(43*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(43*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_290_test (h0 : cos((-4*pi)/2)≠ 0) (h1 : (1+cos(-4*pi))≠ 0) (h2 : (1+cos((-4)*pi))≠ 0) : sin(-4*pi)/(1 + cos(-4*pi))=- tan(22*pi):=
begin
have : sin((-4) * pi) / (1 + cos((-4) * pi)) = sin(-4*pi)/(1 + cos(-4*pi)),
{
field_simp at *,
},
have : tan(-2*pi) = sin(-4*pi) / ( 1 + cos(-4*pi) ),
{
have : tan(-2*pi) = tan((-4*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = - tan(22*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-2*pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_291_test : cos(-pi)=-(3*sin(-pi/6) - 4*sin(-pi/6)**3)**2 + cos(-pi/2)**2:=
begin
have : -((-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6)) ** 2 + cos(-pi / 2) ** 2 = -(3*sin(-pi/6) - 4*sin(-pi/6)**3)**2 + cos(-pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = - sin(-pi/2) ** 2 + cos(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end




lemma Trigo_293_test : cos(97*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(97*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_294_test : sin(5*pi/6)=sin(pi)*cos(pi/6) + sin(pi/6)*sin(273*pi/2):=
begin
have : sin(pi) * cos(pi / 6) - sin(pi / 6) * -sin(273 * pi / 2) = sin(pi)*cos(pi/6) + sin(pi/6)*sin(273*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -sin(273*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/6) = sin(pi) * cos(pi/6) - sin(pi/6) * cos(pi),
{
have : sin(5*pi/6) = sin((pi) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_295_test : tan(163*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = tan(163*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_296_test : cos(4*pi/3)=cos(pi/3)*cos(pi) + sin(pi/3)*cos(341*pi/2):=
begin
have : -sin(pi / 3) * -cos(341 * pi / 2) + cos(pi / 3) * cos(pi) = cos(pi/3)*cos(pi) + sin(pi/3)*cos(341*pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -cos(341*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi/3) = - sin(pi/3) * sin(pi) + cos(pi/3) * cos(pi),
{
have : cos(4*pi/3) = cos((pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_297_test : sin(156*pi)=0:=
begin
have : cos(pi/2) = sin(156*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_298_test : sin(14*pi)=- cos(297*pi/2):=
begin
have : cos(pi/2) = sin(14*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(297*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_299_test : -1 + cos(-pi) + 2*cos(pi/6)**2=2 * cos(2*pi/3) * cos(-pi/3):=
begin
have : 2 * cos(pi / 6) ** 2 - 1 + cos(-pi) = -1 + cos(-pi) + 2*cos(pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 2 * cos(pi/6) ** 2 - 1,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) + cos(-pi) = 2 * cos(2*pi/3) * cos(-pi/3),
{
rw cos_add_cos,
have : cos(((pi/3) + (-pi))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (-pi))/2) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_300_test : cos(67*pi/2)=- sin(186*pi):=
begin
have : sin(-2*pi) = cos(67*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(186*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_301_test : sin(pi) ** 2=1 - cos(40*pi)**2:=
begin
have : 1 - (-cos(40 * pi)) ** 2 = 1 - cos(40*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -cos(40*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) ** 2 = 1 - cos(pi) ** 2,
{
rw sin_sq,
},
rw this,
end




lemma Trigo_303_test : cos(113*pi)**2=1 - cos(-pi/2) ** 2:=
begin
have : sin(-pi/2) = cos(113*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) ** 2 = 1 - cos(-pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_304_test : -cos(154*pi/3)=cos(199*pi/3):=
begin
have : cos(pi/3) = -cos(154*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(199*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_305_test : sin(pi/6) ** 2=1 - sin(532*pi/3)**2:=
begin
have : 1 - (-sin(532 * pi / 3)) ** 2 = 1 - sin(532*pi/3)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -sin(532*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 - cos(pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end




lemma Trigo_307_test (h0 : cos(pi/6)≠ 0) : -cos(412*pi/3)/cos(pi/6)=tan(pi/6):=
begin
have : sin(pi/6) = -cos(412*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) / cos(pi/6) = tan(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_309_test : -1 + 2*sin(-pi)**2 + cos(pi/3)=- 2 * sin(7*pi/6) * sin(-5*pi/6):=
begin
have : cos(pi / 3) - (1 - 2 * sin(-pi) ** 2) = -1 + 2*sin(-pi)**2 + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = 1 - 2 * sin(-pi) ** 2,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) - cos(-2*pi) = - 2 * sin(7*pi/6) * sin(-5*pi/6),
{
rw cos_sub_cos,
have : sin(((pi/3) + (-2*pi))/2) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (-2*pi))/2) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_311_test : -sin(181*pi/2)=- sin(253*pi/2):=
begin
have : cos(-pi) = -sin(181*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(253*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_312_test : -2*sin(-pi/2)**2 + cos(-pi/6) + 1=2 * cos(-5*pi/12) * cos(-7*pi/12):=
begin
have : 1 - 2 * sin(-pi / 2) ** 2 + cos(-pi / 6) = -2*sin(-pi/2)**2 + cos(-pi/6) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = 1 - 2 * sin(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi) + cos(-pi/6) = 2 * cos(-5*pi/12) * cos(-7*pi/12),
{
rw cos_add_cos,
have : cos(((-pi) + (-pi/6))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (-pi/6))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_314_test : -sin(115*pi/2)=4 * cos(-2*pi) ** 3 - 3 * cos(-2*pi):=
begin
have : cos(-6*pi) = -sin(115*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-6*pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-6*pi) = 4 * cos(-2*pi) ** 3 - 3 * cos(-2*pi),
{
have : cos(-6*pi) = cos(3*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_315_test : (-sin(-pi/4)**2 + cos(-pi/4)**2)*cos(-2*pi)=cos(-3*pi/2) / 2 + cos(-5*pi/2) / 2:=
begin
have : cos((-2) * pi) * (-sin(-pi / 4) ** 2 + cos(-pi / 4) ** 2) = (-sin(-pi/4)**2 + cos(-pi/4)**2)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(-pi/4) ** 2 + cos(-pi/4) ** 2,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) * cos(-pi/2) = cos(-3*pi/2) / 2 + cos(-5*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (-pi/2)) = cos(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (-pi/2)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_316_test : -cos(517*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(517*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_317_test : sin(110*pi/3)=sin(313*pi/3):=
begin
have : cos(pi/6) = sin(110*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(313*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_318_test : cos(pi)=-sin(369*pi/2):=
begin
have : sin(323*pi/2) = -sin(369*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (323*pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = sin(323*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_319_test (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : cos(13*pi/6)=-sin(pi/3)*sin(2*pi)/(2*cos(pi/6)) + cos(pi/6)*cos(2*pi):=
begin
have : -(sin(pi / 3) / (2 * cos(pi / 6))) * sin(2 * pi) + cos(pi / 6) * cos(2 * pi) = -sin(pi/3)*sin(2*pi)/(2*cos(pi/6)) + cos(pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = sin(pi/3) / ( 2 * cos(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(13*pi/6) = - sin(pi/6) * sin(2*pi) + cos(pi/6) * cos(2*pi),
{
have : cos(13*pi/6) = cos((pi/6) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_320_test (h0 : cos(-7*pi/6)≠ 0) (h1 : cos(-pi)≠ 0) (h2 : (tan(-7*pi/6)*tan(-pi)+1)≠ 0) (h3 : (1+tan((-7)*pi/6)*tan(-pi))≠ 0) : (tan(-7*pi/6) - tan(-pi))/(tan(-7*pi/6)*tan(-pi) + 1)=- 1 / tan(181*pi/3):=
begin
have : (tan((-7) * pi / 6) - tan(-pi)) / (1 + tan((-7) * pi / 6) * tan(-pi)) = (tan(-7*pi/6) - tan(-pi))/(tan(-7*pi/6)*tan(-pi) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = ( tan(-7*pi/6) - tan(-pi) ) / ( 1 + tan(-7*pi/6) * tan(-pi) ),
{
have : tan(-pi/6) = tan((-7*pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - 1 / tan(181*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_321_test : cos(719*pi/6)=- cos(413*pi/6):=
begin
have : cos(pi/6) = cos(719*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(413*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_324_test : sin(pi/6)=sin(-871*pi/6):=
begin
have : - -sin((-871) * pi / 6) = sin(-871*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(548*pi/3) = -sin(-871*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (548*pi/3) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(548*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_325_test : cos(156*pi)=2 * cos(pi) ** 2 - 1:=
begin
have : cos(2*pi) = cos(156*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 2 * cos(pi) ** 2 - 1,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
rw this,
end


lemma Trigo_326_test (h0 : cos(pi/3)≠ 0) (h1 : cos(-pi/6)≠ 0) (h2 : (tan(-pi/6)*tan(pi/3)+1)≠ 0) (h3 : (1+tan(pi/3)*tan(-pi/6))≠ 0) : (-tan(-pi/6) + tan(pi/3))/(tan(-pi/6)*tan(pi/3) + 1)=- tan(171*pi/2):=
begin
have : (tan(pi / 3) - tan(-pi / 6)) / (1 + tan(pi / 3) * tan(-pi / 6)) = (-tan(-pi/6) + tan(pi/3))/(tan(-pi/6)*tan(pi/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = ( tan(pi/3) - tan(-pi/6) ) / ( 1 + tan(pi/3) * tan(-pi/6) ),
{
have : tan(pi/2) = tan((pi/3) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - tan(171*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_327_test : sin(79*pi)=cos(-3*pi/2):=
begin
have : sin(2*pi) = sin(79*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(-3*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_328_test : -sin(423*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -sin(423*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/4) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_329_test : -sin(35*pi/6)=1 / 2:=
begin
have : cos(pi/3) = -sin(35*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_330_test : -sin(409*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(409*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_331_test : sin(-pi/2)=cos(75*pi):=
begin
have : cos(77*pi) = cos(75*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (77*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = cos(77*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_332_test : -sin(143*pi/2)=4 * cos(2*pi) ** 3 - 3 * cos(2*pi):=
begin
have : cos(6*pi) = -sin(143*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (6*pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(6*pi) = 4 * cos(2*pi) ** 3 - 3 * cos(2*pi),
{
have : cos(6*pi) = cos(3*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_333_test : sin(151*pi/2) - sin(pi/6)=2 * sin(-pi/3) * cos(-pi/6):=
begin
have : sin(-pi/2) = sin(151*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) - sin(pi/6) = 2 * sin(-pi/3) * cos(-pi/6),
{
rw sin_sub_sin,
have : cos(((-pi/2) + (pi/6))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (pi/6))/2) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end






lemma Trigo_336_test : sin(-pi/6) - 2*sin(-pi/2)*cos(-pi/2)=2 * sin(5*pi/12) * cos(-7*pi/12):=
begin
have : sin(-pi) = 2 * sin(-pi/2) * cos(-pi/2),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) - sin(-pi) = 2 * sin(5*pi/12) * cos(-7*pi/12),
{
rw sin_sub_sin,
have : cos(((-pi/6) + (-pi))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (-pi))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_337_test : -cos(229*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(229*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_338_test : (-3*cos(pi/6) + 4*cos(pi/6)**3)*cos(-2*pi)=cos(-5*pi/2) / 2 + cos(-3*pi/2) / 2:=
begin
have : cos((-2) * pi) * (4 * cos(pi / 6) ** 3 - 3 * cos(pi / 6)) = (-3*cos(pi/6) + 4*cos(pi/6)**3)*cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 4 * cos(pi/6) ** 3 - 3 * cos(pi/6),
{
have : cos(pi/2) = cos(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) * cos(pi/2) = cos(-5*pi/2) / 2 + cos(-3*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (pi/2)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/2)) = cos(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_339_test : sin(-pi/3)=-2*sin(-pi/6)*sin(119*pi/3):=
begin
have : 2 * sin(-pi / 6) * -sin(119 * pi / 3) = -2*sin(-pi/6)*sin(119*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(119*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = 2 * sin(-pi/6) * cos(-pi/6),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_340_test : sin(2333*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = sin(2333*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_341_test : sin(50*pi)=sin(73*pi):=
begin
have : sin(-2*pi) = sin(50*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(73*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_342_test : sin(-pi)=1 - 2*sin(103*pi/4)**2:=
begin
have : cos(103*pi/2) = 1 - 2 * sin(103*pi/4) ** 2,
{
have : cos(103*pi/2) = cos(2*(103*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(103*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_343_test : cos(-pi/3)=-cos(-164*pi/3):=
begin
have : -cos((-164) * pi / 3) = -cos(-164*pi/3),
{
field_simp at *,
},
have : sin(517*pi/6) = -cos(-164*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (517*pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = sin(517*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_344_test : -sin(150*pi)=0:=
begin
have : cos(pi/2) = -sin(150*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_345_test : sin(2*pi)=-cos(-2*pi)*cos(21*pi/2) + sin(-2*pi)*sin(21*pi/2):=
begin
have : -(-sin(21 * pi / 2) * sin((-2) * pi) + cos(21 * pi / 2) * cos((-2) * pi)) = -cos(-2*pi)*cos(21*pi/2) + sin(-2*pi)*sin(21*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(17*pi/2) = -sin(21*pi/2) * sin(-2*pi) + cos(21*pi/2) * cos(-2*pi),
{
have : cos(17*pi/2) = cos((21*pi/2) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = - cos(17*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_346_test : -cos(172*pi/3) + cos(-2*pi)=2 * cos(-5*pi/6) * cos(-7*pi/6):=
begin
have : cos((-2) * pi) + -cos(172 * pi / 3) = -cos(172*pi/3) + cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(172*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(-pi/3) = 2 * cos(-5*pi/6) * cos(-7*pi/6),
{
rw cos_add_cos,
have : cos(((-2*pi) + (-pi/3))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (-pi/3))/2) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_347_test : cos(167*pi/6)=sin(-pi) * cos(pi/3) - sin(pi/3) * cos(-pi):=
begin
have : sin(-4*pi/3) = cos(167*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-4*pi/3) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-4*pi/3) = sin(-pi) * cos(pi/3) - sin(pi/3) * cos(-pi),
{
have : sin(-4*pi/3) = sin((-pi) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_348_test : -sin(2273*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -sin(2273*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end




lemma Trigo_350_test : cos(449*pi/3)=sin(pi/6) * cos(2*pi) - sin(2*pi) * cos(pi/6):=
begin
have : sin(-11*pi/6) = cos(449*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-11*pi/6) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-11*pi/6) = sin(pi/6) * cos(2*pi) - sin(2*pi) * cos(pi/6),
{
have : sin(-11*pi/6) = sin((pi/6) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_351_test : -cos(104*pi)=sin(99*pi/2):=
begin
have : cos(-pi) = -cos(104*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(99*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_352_test : cos(329*pi/3)=- sin(95*pi/6):=
begin
have : cos(-pi/3) = cos(329*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - sin(95*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_353_test : tan(151*pi/2)=- 1 / tan(82*pi):=
begin
have : tan(pi/2) = tan(151*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - 1 / tan(82*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_355_test : -sin(65*pi/2)=sin(63*pi/2):=
begin
have : cos(pi) = -sin(65*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(63*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_357_test : sin(215*pi/3)=sin(-pi) * sin(-pi/6) + cos(-pi) * cos(-pi/6):=
begin
have : cos(-5*pi/6) = sin(215*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-5*pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/6) = sin(-pi) * sin(-pi/6) + cos(-pi) * cos(-pi/6),
{
have : cos(-5*pi/6) = cos((-pi) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_358_test (h0 : cos(13*pi/12)≠ 0) (h1 : cos(pi)≠ 0) (h2 : (1+tan(13*pi/12)*tan(pi))≠ 0) (h3 : (tan(pi)*tan(13*pi/12)+1)≠ 0) : (-tan(pi) + tan(13*pi/12))/(tan(pi)*tan(13*pi/12) + 1)=2 - sqrt( 3 ):=
begin
have : (tan(13 * pi / 12) - tan(pi)) / (1 + tan(13 * pi / 12) * tan(pi)) = (-tan(pi) + tan(13*pi/12))/(tan(pi)*tan(13*pi/12) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(13*pi/12) - tan(pi) ) / ( 1 + tan(13*pi/12) * tan(pi) ),
{
have : tan(pi/12) = tan((13*pi/12) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_359_test (h0 : cos(-pi)≠ 0) : -sin(121*pi)=sin(-2*pi) / ( 2 * cos(-pi) ):=
begin
have : sin(-pi) = -sin(121*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(-2*pi) / ( 2 * cos(-pi) ),
{
have : sin(-2*pi) = sin(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
rw this,
end


lemma Trigo_360_test : sin(-pi) - sin(-pi/6)=2*sin(-5*pi/12)*sin(743*pi/12):=
begin
have : 2 * sin((-5) * pi / 12) * sin(743 * pi / 12) = 2*sin(-5*pi/12)*sin(743*pi/12),
{
field_simp at *,
},
have : cos(-7*pi/12) = sin(743*pi/12),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-7*pi/12) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) - sin(-pi/6) = 2 * sin(-5*pi/12) * cos(-7*pi/12),
{
rw sin_sub_sin,
have : cos(((-pi) + (-pi/6))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (-pi/6))/2) = sin(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_361_test (h0 : sin(3*pi/4)≠ 0) (h1 : (2*sin(3*pi/4))≠ 0) (h2 : sin(3*pi/4)≠ 0) : sin(2*pi) + sin(pi/2)=sin(5*pi/4)*sin(3*pi/2)/sin(3*pi/4):=
begin
have : 2 * sin(5 * pi / 4) * (sin(3 * pi / 2) / (2 * sin(3 * pi / 4))) = sin(5*pi/4)*sin(3*pi/2)/sin(3*pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/4) = sin(3*pi/2) / ( 2 * sin(3*pi/4) ),
{
have : sin(3*pi/2) = sin(2*(3*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) + sin(pi/2) = 2 * sin(5*pi/4) * cos(3*pi/4),
{
rw sin_add_sin,
have : sin(((2*pi) + (pi/2))/2) = sin(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (pi/2))/2) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_362_test : -sin(-pi/3)*cos(5*pi/12) + sin(5*pi/12)*cos(-pi/3)=sqrt( 2 ) / 2:=
begin
have : sin(5 * pi / 12) * cos(-pi / 3) - sin(-pi / 3) * cos(5 * pi / 12) = -sin(-pi/3)*cos(5*pi/12) + sin(5*pi/12)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(5*pi/12) * cos(-pi/3) - sin(-pi/3) * cos(5*pi/12),
{
have : sin(3*pi/4) = sin((5*pi/12) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_363_test : -sin(167*pi/3)=cos(445*pi/6):=
begin
have : cos(pi/6) = -sin(167*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(445*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_365_test : cos(193*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = cos(193*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_366_test : -tan(116*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(116*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_367_test : -sin(-5*pi/6)*sin(pi) + cos(-5*pi/6)*cos(pi) + cos(-2*pi)=2 * cos(-13*pi/12) * cos(-11*pi/12):=
begin
have : cos((-2) * pi) + (-sin((-5) * pi / 6) * sin(pi) + cos((-5) * pi / 6) * cos(pi)) = -sin(-5*pi/6)*sin(pi) + cos(-5*pi/6)*cos(pi) + cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(-5*pi/6) * sin(pi) + cos(-5*pi/6) * cos(pi),
{
have : cos(pi/6) = cos((-5*pi/6) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(pi/6) = 2 * cos(-13*pi/12) * cos(-11*pi/12),
{
rw cos_add_cos,
have : cos(((-2*pi) + (pi/6))/2) = cos(-11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi/6))/2) = cos(-13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_368_test : -sin(331*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = -sin(331*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/6) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_369_test : sin(27*pi/2)=- sin(301*pi/2):=
begin
have : cos(pi) = sin(27*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - sin(301*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_370_test : -sin(33*pi/2)=sin(367*pi/2):=
begin
have : cos(-pi) = -sin(33*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(367*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_371_test : sin(97*pi)**2 + cos(-pi)**2=1:=
begin
have : (-sin(97 * pi)) ** 2 + cos(-pi) ** 2 = sin(97*pi)**2 + cos(-pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -sin(97*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) ** 2 + cos(-pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_372_test : sin(-pi/3) + sin(0)*cos(-pi/6) - sin(-pi/6)*cos(0)=2 * sin(-pi/12) * cos(pi/4):=
begin
have : sin(0) * cos(-pi / 6) - sin(-pi / 6) * cos(0) + sin(-pi / 3) = sin(-pi/3) + sin(0)*cos(-pi/6) - sin(-pi/6)*cos(0),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(0) * cos(-pi/6) - sin(-pi/6) * cos(0),
{
have : sin(pi/6) = sin((0) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) + sin(-pi/3) = 2 * sin(-pi/12) * cos(pi/4),
{
rw sin_add_sin,
have : sin(((pi/6) + (-pi/3))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/6) - (-pi/3))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_373_test (h0 : cos(pi)≠ 0) : sin(pi)/cos(pi)=tan(91*pi):=
begin
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = tan(91*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_374_test : sin(83*pi)=2 * sin(pi) * cos(pi):=
begin
have : sin(2*pi) = sin(83*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = 2 * sin(pi) * cos(pi),
{
have : sin(2*pi) = sin(2*(pi)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
end


lemma Trigo_375_test : (sin(5*pi/3)*cos(-pi/3) - sin(-pi/3)*cos(5*pi/3))*cos(pi/2)=- sin(-3*pi/2) / 2 + sin(5*pi/2) / 2:=
begin
have : sin(2*pi) = sin(5*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(5*pi/3),
{
have : sin(2*pi) = sin((5*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(pi/2) = - sin(-3*pi/2) / 2 + sin(5*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/2) + (2*pi)) = sin(5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (2*pi)) = sin(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_376_test : -cos(1135*pi/6)=cos(659*pi/6):=
begin
have : sin(pi/3) = -cos(1135*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(659*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_377_test : -sin(586*pi/3)*cos(-pi/2)=cos(-pi/3) / 2 + cos(-2*pi/3) / 2:=
begin
have : cos(-pi / 2) * -sin(586 * pi / 3) = -sin(586*pi/3)*cos(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(586*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) * cos(-pi/6) = cos(-pi/3) / 2 + cos(-2*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((-pi/2) + (-pi/6)) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (-pi/6)) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_378_test : -cos(-pi/3)*cos(381*pi/2)=cos(5*pi/6) / 2 + cos(pi/6) / 2:=
begin
have : -cos(381 * pi / 2) * cos(-pi / 3) = -cos(-pi/3)*cos(381*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(381*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) * cos(-pi/3) = cos(5*pi/6) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
have : cos((pi/2) + (-pi/3)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (-pi/3)) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_379_test : cos(323*pi/6)=cos(457*pi/6):=
begin
have : cos(pi/6) = cos(323*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(457*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_380_test (h0 : cos((pi/3)/2)≠ 0) (h1 : sin(pi/3)≠ 0) : (1 - cos(pi/3))/sin(pi/3)=- 1 / tan(8*pi/3):=
begin
have : tan(pi/6) = ( 1 - cos(pi/3) ) / sin(pi/3),
{
have : tan(pi/6) = tan((pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = - 1 / tan(8*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_381_test : sin(pi)=-cos(275*pi/4)**2 + sin(275*pi/4)**2:=
begin
have : -(-sin(275 * pi / 4) ** 2 + cos(275 * pi / 4) ** 2) = -cos(275*pi/4)**2 + sin(275*pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(275*pi/2) = -sin(275*pi/4) ** 2 + cos(275*pi/4) ** 2,
{
have : cos(275*pi/2) = cos(2*(275*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = - cos(275*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_382_test (h0 : cos(25*pi/12)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (1+tan(25*pi/12)*tan(2*pi))≠ 0) (h3 : (tan(2*pi)*tan(25*pi/12)+1)≠ 0) : (-tan(2*pi) + tan(25*pi/12))/(tan(2*pi)*tan(25*pi/12) + 1)=2 - sqrt( 3 ):=
begin
have : (tan(25 * pi / 12) - tan(2 * pi)) / (1 + tan(25 * pi / 12) * tan(2 * pi)) = (-tan(2*pi) + tan(25*pi/12))/(tan(2*pi)*tan(25*pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(25*pi/12) - tan(2*pi) ) / ( 1 + tan(25*pi/12) * tan(2*pi) ),
{
have : tan(pi/12) = tan((25*pi/12) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_383_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : sin(pi)/(2*cos(pi/2))=- sin(363*pi/2):=
begin
have : sin(pi/2) = sin(pi) / ( 2 * cos(pi/2) ),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(363*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_384_test : sin(146*pi)*cos(-pi)=cos(pi/2) / 2 + cos(-3*pi/2) / 2:=
begin
have : cos(-pi/2) = sin(146*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) * cos(-pi) = cos(pi/2) / 2 + cos(-3*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-pi/2) + (-pi)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (-pi)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_385_test (h0 : cos(-pi)≠ 0) : (-sin(pi)*cos(0) + sin(0)*cos(pi))/cos(-pi)=tan(-pi):=
begin
have : (sin(0) * cos(pi) - sin(pi) * cos(0)) / cos(-pi) = (-sin(pi)*cos(0) + sin(0)*cos(pi))/cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(0) * cos(pi) - sin(pi) * cos(0),
{
have : sin(-pi) = sin((0) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) / cos(-pi) = tan(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_386_test : -sin(144*pi)=sin(124*pi):=
begin
have : cos(-pi/2) = -sin(144*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(124*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_388_test : sin(145*pi/6)=cos(559*pi/3):=
begin
have : cos(pi/3) = sin(145*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(559*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_389_test : cos(-pi)=sin(47*pi/3)*cos(pi/6) - sin(pi/6)*cos(47*pi/3):=
begin
have : sin(31*pi/2) = sin(47*pi/3) * cos(pi/6) - sin(pi/6) * cos(47*pi/3),
{
have : sin(31*pi/2) = sin((47*pi/3) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(31*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_391_test : -1 + 2*cos(pi)**2=- sin(291*pi/2):=
begin
have : 2 * cos(pi) ** 2 - 1 = -1 + 2*cos(pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 2 * cos(pi) ** 2 - 1,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - sin(291*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_392_test (h0 : cos(-6*pi)≠ 0) (h1 : (2*cos(-6*pi))≠ 0) (h2 : (2*cos((-6)*pi))≠ 0) : sin(-12*pi)/(2*cos(-6*pi))=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : sin((-12) * pi) / (2 * cos((-6) * pi)) = sin(-12*pi)/(2*cos(-6*pi)),
{
field_simp at *,
},
have : sin(-6*pi) = sin(-12*pi) / ( 2 * cos(-6*pi) ),
{
have : sin(-12*pi) = sin(2*(-6*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-6*pi) = - 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi),
{
have : sin(-6*pi) = sin(3*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end




lemma Trigo_394_test : sin(197*pi)=sin(21*pi):=
begin
have : sin(2*pi) = sin(197*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(21*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_395_test : sin(32*pi/3)=- cos(271*pi/6):=
begin
have : cos(pi/6) = sin(32*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(271*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_396_test : -sin(-pi/6)**2 + cos(-pi/6)**2=cos(245*pi/3):=
begin
have : cos(-pi/3) = -sin(-pi/6) ** 2 + cos(-pi/6) ** 2,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(245*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_398_test : sin(2*pi)=sin(330*pi):=
begin
have : - -sin(330 * pi) = sin(330*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(369*pi/2) = -sin(330*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (369*pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = - cos(369*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_399_test : -sin(-pi)*sin(7*pi/6) + cos(-pi)*cos(7*pi/6)=sin(-pi/3) * sin(-pi/2) + cos(-pi/3) * cos(-pi/2):=
begin
have : -sin(7 * pi / 6) * sin(-pi) + cos(7 * pi / 6) * cos(-pi) = -sin(-pi)*sin(7*pi/6) + cos(-pi)*cos(7*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(7*pi/6) * sin(-pi) + cos(7*pi/6) * cos(-pi),
{
have : cos(pi/6) = cos((7*pi/6) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(-pi/3) * sin(-pi/2) + cos(-pi/3) * cos(-pi/2),
{
have : cos(pi/6) = cos((-pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_400_test (h0 : sin(87*pi/2)≠ 0) : sin(-pi)/sin(87*pi/2)=tan(-pi):=
begin
have : cos(-pi) = sin(87*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) / cos(-pi) = tan(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_401_test : cos(-2*pi) ** 2=1 - (sin(-pi)*cos(pi) - sin(pi)*cos(-pi))**2:=
begin
have : sin(-2*pi) = sin(-pi) * cos(pi) - sin(pi) * cos(-pi),
{
have : sin(-2*pi) = sin((-pi) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) ** 2 = 1 - sin(-2*pi) ** 2,
{
rw cos_sq',
},
rw this,
end






lemma Trigo_404_test : cos(769*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(769*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_405_test : -cos(110*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(110*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_406_test (h0 : cos((4*pi)/2)≠ 0) (h1 : sin(4*pi)≠ 0) : sin(2*pi) / cos(2*pi)=(1 - cos(4*pi))/sin(4*pi):=
begin
have : tan(2*pi) = ( 1 - cos(4*pi) ) / sin(4*pi),
{
have : tan(2*pi) = tan((4*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) / cos(2*pi) = tan(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_408_test : -cos(-pi/2) - cos(395*pi/2)=- 2 * sin(pi/2) * sin(0):=
begin
have : -cos(395 * pi / 2) - cos(-pi / 2) = -cos(-pi/2) - cos(395*pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(395*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) - cos(-pi/2) = - 2 * sin(pi/2) * sin(0),
{
rw cos_sub_cos,
have : sin(((pi/2) + (-pi/2))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (-pi/2))/2) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_409_test : sin(129*pi/2)=cos(8*pi):=
begin
have : sin(pi/2) = sin(129*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(8*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_410_test : -4*sin(2*pi/3)**3 + 3*sin(2*pi/3)=- sin(171*pi):=
begin
have : (-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3) = -4*sin(2*pi/3)**3 + 3*sin(2*pi/3),
{
field_simp at *,
},
have : sin(2*pi) = -4 * sin(2*pi/3) ** 3 + 3 * sin(2*pi/3),
{
have : sin(2*pi) = sin(3*(2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(171*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_411_test : sin(155*pi)=cos(225*pi/2):=
begin
have : sin(2*pi) = sin(155*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(225*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_413_test : cos(-pi/6)=cos(-pi/3)*cos(pi/6) - (3*sin(-pi/9) - 4*sin(-pi/9)**3)*sin(pi/6):=
begin
have : -sin(pi / 6) * ((-4) * sin(-pi / 9) ** 3 + 3 * sin(-pi / 9)) + cos(pi / 6) * cos(-pi / 3) = cos(-pi/3)*cos(pi/6) - (3*sin(-pi/9) - 4*sin(-pi/9)**3)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = -4 * sin(-pi/9) ** 3 + 3 * sin(-pi/9),
{
have : sin(-pi/3) = sin(3*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(pi/6) * sin(-pi/3) + cos(pi/6) * cos(-pi/3),
{
have : cos(-pi/6) = cos((pi/6) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_414_test (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : sin(2*pi)*cos(-2*pi)/(2*cos(pi))=- sin(-3*pi) / 2 + sin(-pi) / 2:=
begin
have : sin(2 * pi) / (2 * cos(pi)) * cos((-2) * pi) = sin(2*pi)*cos(-2*pi)/(2*cos(pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(2*pi) / ( 2 * cos(pi) ),
{
have : sin(2*pi) = sin(2*(pi)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(-2*pi) = - sin(-3*pi) / 2 + sin(-pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-2*pi) + (pi)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi)) = sin(-3*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_416_test : cos(103*pi/2)=- 4 * sin(-pi) ** 3 + 3 * sin(-pi):=
begin
have : sin(-3*pi) = cos(103*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-3*pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi) = - 4 * sin(-pi) ** 3 + 3 * sin(-pi),
{
have : sin(-3*pi) = sin(3*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_417_test : (4*cos(2*pi/3)**3 - 3*cos(2*pi/3))*sin(pi/3)=sin(-5*pi/3) / 2 + sin(7*pi/3) / 2:=
begin
have : sin(pi / 3) * (4 * cos(2 * pi / 3) ** 3 - 3 * cos(2 * pi / 3)) = (4*cos(2*pi/3)**3 - 3*cos(2*pi/3))*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 4 * cos(2*pi/3) ** 3 - 3 * cos(2*pi/3),
{
have : cos(2*pi) = cos(3*(2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(2*pi) = sin(-5*pi/3) / 2 + sin(7*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (2*pi)) = sin(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (2*pi)) = sin(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_418_test : cos(pi) - sin(-5*pi/3)*sin(pi/3) - cos(-5*pi/3)*cos(pi/3)=- 2 * sin(3*pi/2) * sin(-pi/2):=
begin
have : cos(pi) - (sin((-5) * pi / 3) * sin(pi / 3) + cos((-5) * pi / 3) * cos(pi / 3)) = cos(pi) - sin(-5*pi/3)*sin(pi/3) - cos(-5*pi/3)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(-5*pi/3) * sin(pi/3) + cos(-5*pi/3) * cos(pi/3),
{
have : cos(-2*pi) = cos((-5*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) - cos(-2*pi) = - 2 * sin(3*pi/2) * sin(-pi/2),
{
rw cos_sub_cos,
have : sin(((pi) + (-2*pi))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi) - (-2*pi))/2) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_419_test : -sin(302*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(302*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_420_test : -cos(295*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -cos(295*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3*pi/4) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_421_test : (-sin(-11*pi/6)*sin(2*pi) + cos(-11*pi/6)*cos(2*pi))*sin(pi/3)=- sin(-pi/6) / 2 + sin(pi/2) / 2:=
begin
have : sin(pi / 3) * (-sin((-11) * pi / 6) * sin(2 * pi) + cos((-11) * pi / 6) * cos(2 * pi)) = (-sin(-11*pi/6)*sin(2*pi) + cos(-11*pi/6)*cos(2*pi))*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(-11*pi/6) * sin(2*pi) + cos(-11*pi/6) * cos(2*pi),
{
have : cos(pi/6) = cos((-11*pi/6) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(pi/6) = - sin(-pi/6) / 2 + sin(pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/6) + (pi/3)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (pi/3)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_422_test : -cos(279*pi/2)=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : sin(-6*pi) = -cos(279*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-6*pi) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-6*pi) = - 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi),
{
have : sin(-6*pi) = sin(3*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_423_test : -sin(56*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(56*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end






lemma Trigo_426_test (h0 : cos(-5*pi/6)≠ 0) (h1 : (2*cos(-5*pi/6))≠ 0) (h2 : (2*cos((-5)*pi/6))≠ 0) : sin(-5*pi/3)/(2*cos(-5*pi/6))=sin(-pi/3) * cos(pi/2) - sin(pi/2) * cos(-pi/3):=
begin
have : sin((-5) * pi / 3) / (2 * cos((-5) * pi / 6)) = sin(-5*pi/3)/(2*cos(-5*pi/6)),
{
field_simp at *,
},
have : sin(-5*pi/6) = sin(-5*pi/3) / ( 2 * cos(-5*pi/6) ),
{
have : sin(-5*pi/3) = sin(2*(-5*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/6) = sin(-pi/3) * cos(pi/2) - sin(pi/2) * cos(-pi/3),
{
have : sin(-5*pi/6) = sin((-pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_427_test : sin(227*pi/2)**2=cos(-2*pi) / 2 + 1 / 2:=
begin
have : cos(-pi) = sin(227*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) ** 2 = cos(-2*pi) / 2 + 1 / 2,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_428_test : cos(3*pi)=cos(pi)*cos(2*pi) + cos(3*pi)/2 - cos(-pi)/2:=
begin
have : -(cos(-pi) / 2 - cos(3 * pi) / 2) + cos(2 * pi) * cos(pi) = cos(pi)*cos(2*pi) + cos(3*pi)/2 - cos(-pi)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * sin(2*pi) = cos(-pi) / 2 - cos(3*pi) / 2,
{
rw sin_mul_sin,
have : cos((pi) + (2*pi)) = cos(3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (2*pi)) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -(sin(pi) * sin(2*pi)) = -sin(2*pi)*sin(pi),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(3*pi) = - sin(2*pi) * sin(pi) + cos(2*pi) * cos(pi),
{
have : cos(3*pi) = cos((2*pi) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_429_test : -sin(47*pi/2)=- cos(35*pi):=
begin
have : cos(-2*pi) = -sin(47*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - cos(35*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_430_test : -sin(323*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -sin(323*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_431_test (h0 : tan(88*pi/3)≠ 0) : 1/tan(88*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(88*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_432_test : -sin(83*pi/6)=sin(577*pi/6):=
begin
have : sin(pi/6) = -sin(83*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(577*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_433_test : cos(2*pi) - cos(pi)=-2*(-4*sin(pi/6)**3 + 3*sin(pi/6))*sin(3*pi/2):=
begin
have : (-2) * ((-4) * sin(pi / 6) ** 3 + 3 * sin(pi / 6)) * sin(3 * pi / 2) = -2*(-4*sin(pi/6)**3 + 3*sin(pi/6))*sin(3*pi/2),
{
field_simp at *,
},
have : sin(pi/2) = -4 * sin(pi/6) ** 3 + 3 * sin(pi/6),
{
have : sin(pi/2) = sin(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) - cos(pi) = - 2 * sin(pi/2) * sin(3*pi/2),
{
rw cos_sub_cos,
have : sin(((2*pi) + (pi))/2) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi) - (pi))/2) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_434_test (h0 : tan(104*pi)≠ 0) (h1 : ((-1)/tan(104*pi))≠ 0) : tan(-2*pi)=tan(104*pi):=
begin
have : (-1) / ((-1) / tan(104 * pi)) = tan(104*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(189*pi/2) = -1 / tan(104*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (189*pi/2) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-2*pi) = - 1 / tan(189*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_435_test : cos(203*pi/3)=2 * cos(pi/6) ** 2 - 1:=
begin
have : cos(pi/3) = cos(203*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 2 * cos(pi/6) ** 2 - 1,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_436_test : sin(709*pi/6)=cos(161*pi/3):=
begin
have : sin(pi/6) = sin(709*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(161*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_439_test : -sin(979*pi/6)=cos(503*pi/3):=
begin
have : sin(pi/6) = -sin(979*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(503*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_442_test : cos(7*pi/6)=cos(-pi)*cos(pi/6) + (-4*sin(pi/18)**3 + 3*sin(pi/18))*sin(-pi):=
begin
have : ((-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18)) * sin(-pi) + cos(pi / 6) * cos(-pi) = cos(-pi)*cos(pi/6) + (-4*sin(pi/18)**3 + 3*sin(pi/18))*sin(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -4 * sin(pi/18) ** 3 + 3 * sin(pi/18),
{
have : sin(pi/6) = sin(3*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/6) = sin(pi/6) * sin(-pi) + cos(pi/6) * cos(-pi),
{
have : cos(7*pi/6) = cos((pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_443_test : tan(485*pi/6)=tan(239*pi/6):=
begin
have : tan(-pi/6) = tan(485*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = tan(239*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_446_test (h0 : tan(39*pi/2)≠ 0) : 1/tan(39*pi/2)=1 / tan(93*pi/2):=
begin
have : tan(pi) = 1 / tan(39*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(93*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_447_test : cos(-pi/6)=-cos(355*pi/6):=
begin
have : sin(64*pi/3) = cos(355*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (64*pi/3) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(64*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_448_test : -cos(-2*pi)*cos(25*pi/2)=- sin(-4*pi) / 2 + sin(0) / 2:=
begin
have : -cos(25 * pi / 2) * cos((-2) * pi) = -cos(-2*pi)*cos(25*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(25*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(-2*pi) = - sin(-4*pi) / 2 + sin(0) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-2*pi) + (2*pi)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (2*pi)) = sin(-4*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_449_test : sin(0)=cos(pi/6)*cos(116*pi/3) + sin(pi/6)*cos(-pi/6):=
begin
have : sin(pi / 6) * cos(-pi / 6) + cos(116 * pi / 3) * cos(pi / 6) = cos(pi/6)*cos(116*pi/3) + sin(pi/6)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = cos(116*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(0) = sin(pi/6) * cos(-pi/6) + sin(-pi/6) * cos(pi/6),
{
have : sin(0) = sin((pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end




lemma Trigo_451_test : -sin(87*pi/2)=4 * cos(2*pi) ** 3 - 3 * cos(2*pi):=
begin
have : cos(6*pi) = -sin(87*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (6*pi) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(6*pi) = 4 * cos(2*pi) ** 3 - 3 * cos(2*pi),
{
have : cos(6*pi) = cos(3*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_452_test : cos(183*pi/2)=sin(116*pi):=
begin
have : sin(2*pi) = cos(183*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(116*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_454_test (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) (h2 : (2*cos(pi/6)**2)≠ 0) : cos(pi/3)=-sin(pi/3)**2/(2*cos(pi/6)**2) + 1:=
begin
have : 1 - 2 * (sin(pi / 3) / (2 * cos(pi / 6))) ** 2 = -sin(pi/3)**2/(2*cos(pi/6)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = sin(pi/3) / ( 2 * cos(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_455_test : cos(441*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = cos(441*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_456_test : -sin(607*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = -sin(607*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_457_test : cos(235*pi/2)=- cos(311*pi/2):=
begin
have : sin(2*pi) = cos(235*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(311*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_458_test (h0 : cos(-7*pi/4)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (1+tan((-7)*pi/4)*tan((-2)*pi))≠ 0) (h3 : (tan(-2*pi)*tan(-7*pi/4)+1)≠ 0) : (-tan(-2*pi) + tan(-7*pi/4))/(tan(-2*pi)*tan(-7*pi/4) + 1)=1:=
begin
have : (tan((-7) * pi / 4) - tan((-2) * pi)) / (1 + tan((-7) * pi / 4) * tan((-2) * pi)) = (-tan(-2*pi) + tan(-7*pi/4))/(tan(-2*pi)*tan(-7*pi/4) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = ( tan(-7*pi/4) - tan(-2*pi) ) / ( 1 + tan(-7*pi/4) * tan(-2*pi) ),
{
have : tan(pi/4) = tan((-7*pi/4) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_459_test (h0 : cos(124*pi/3)≠ 0) (h1 : -cos(124*pi/3)≠ 0) : tan(pi/3)=-sin(pi/3)/cos(124*pi/3):=
begin
have : sin(pi / 3) / -cos(124 * pi / 3) = -sin(pi/3)/cos(124*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(124*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_460_test : sin(pi/2)*sin(27*pi)=sin(pi) / 2 + sin(0) / 2:=
begin
have : cos(-pi/2) = sin(27*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(-pi/2) = sin(pi) / 2 + sin(0) / 2,
{
rw sin_mul_cos,
have : sin((pi/2) + (-pi/2)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (-pi/2)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_461_test : cos(651*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = cos(651*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/4) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_462_test : -sin(100*pi)=0:=
begin
have : sin(pi) = -sin(100*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_463_test : cos(-pi) + cos(-2*pi/3)*cos(-pi/6) + sin(-2*pi/3)*sin(-pi/6)=2 * cos(pi/4) * cos(-3*pi/4):=
begin
have : sin((-2) * pi / 3) * sin(-pi / 6) + cos((-2) * pi / 3) * cos(-pi / 6) + cos(-pi) = cos(-pi) + cos(-2*pi/3)*cos(-pi/6) + sin(-2*pi/3)*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(-2*pi/3) * sin(-pi/6) + cos(-2*pi/3) * cos(-pi/6),
{
have : cos(-pi/2) = cos((-2*pi/3) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) + cos(-pi) = 2 * cos(pi/4) * cos(-3*pi/4),
{
rw cos_add_cos,
have : cos(((-pi/2) + (-pi))/2) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (-pi))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_464_test : cos(-pi) - sin(-4*pi)*sin(2*pi) + cos(-4*pi)*cos(2*pi)=2 * cos(-pi/2) * cos(-3*pi/2):=
begin
have : -sin((-4) * pi) * sin(2 * pi) + cos((-4) * pi) * cos(2 * pi) + cos(-pi) = cos(-pi) - sin(-4*pi)*sin(2*pi) + cos(-4*pi)*cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(-4*pi) * sin(2*pi) + cos(-4*pi) * cos(2*pi),
{
have : cos(-2*pi) = cos((-4*pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(-pi) = 2 * cos(-pi/2) * cos(-3*pi/2),
{
rw cos_add_cos,
have : cos(((-2*pi) + (-pi))/2) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (-pi))/2) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_466_test : sin(pi/6)**2 + (sin(2*pi)*sin(13*pi/6) + cos(2*pi)*cos(13*pi/6))**2=1:=
begin
have : sin(pi / 6) ** 2 + (sin(13 * pi / 6) * sin(2 * pi) + cos(13 * pi / 6) * cos(2 * pi)) ** 2 = sin(pi/6)**2 + (sin(2*pi)*sin(13*pi/6) + cos(2*pi)*cos(13*pi/6))**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(13*pi/6) * sin(2*pi) + cos(13*pi/6) * cos(2*pi),
{
have : cos(pi/6) = cos((13*pi/6) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 + cos(pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_467_test : -cos(7*pi)=cos(132*pi):=
begin
have : sin(pi/2) = -cos(7*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(132*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_468_test : sin(4*pi/3)=-sin(-pi/3)*cos(23*pi) + sin(pi)*cos(-pi/3):=
begin
have : sin(pi) * cos(-pi / 3) - sin(-pi / 3) * cos(23 * pi) = -sin(-pi/3)*cos(23*pi) + sin(pi)*cos(-pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = cos(23*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(4*pi/3) = sin(pi) * cos(-pi/3) - sin(-pi/3) * cos(pi),
{
have : sin(4*pi/3) = sin((pi) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_469_test : sin(-pi)=-cos(-171*pi/2):=
begin
have : -cos((-171) * pi / 2) = -cos(-171*pi/2),
{
field_simp at *,
},
have : cos(273*pi/2) = -cos(-171*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (273*pi/2) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(273*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_470_test : cos(1177*pi/6)=sin(pi) * cos(-pi/3) + sin(-pi/3) * cos(pi):=
begin
have : sin(2*pi/3) = cos(1177*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(pi) * cos(-pi/3) + sin(-pi/3) * cos(pi),
{
have : sin(2*pi/3) = sin((pi) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_471_test (h0 : tan(169*pi/4)≠ 0) : -1/tan(169*pi/4)=- 1:=
begin
have : (-1) / tan(169 * pi / 4) = -1/tan(169*pi/4),
{
field_simp at *,
},
have : tan(3*pi/4) = -1 / tan(169*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (3*pi/4) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_472_test : tan(60*pi)=- tan(85*pi):=
begin
have : tan(pi) = tan(60*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - tan(85*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_473_test (h0 : tan(413*pi/6)≠ 0) : 1/tan(413*pi/6)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = 1 / tan(413*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_474_test : -cos(1117*pi/6)=- sin(451*pi/3):=
begin
have : sin(-pi/3) = -cos(1117*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(451*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_475_test : tan(493*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = tan(493*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_476_test (h0 : cos((-2*pi/3)/2)≠ 0) (h1 : sin(-2*pi/3)≠ 0) (h2 : sin((-2)*pi/3)≠ 0) : (1 - cos(-2*pi/3))/sin(-2*pi/3)=tan(185*pi/3):=
begin
have : (1 - cos((-2) * pi / 3)) / sin((-2) * pi / 3) = (1 - cos(-2*pi/3))/sin(-2*pi/3),
{
field_simp at *,
},
have : tan(-pi/3) = ( 1 - cos(-2*pi/3) ) / sin(-2*pi/3),
{
have : tan(-pi/3) = tan((-2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = tan(185*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (-pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_477_test : -cos(439*pi/6)=- sin(556*pi/3):=
begin
have : sin(pi/3) = -cos(439*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(556*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_478_test : sin(313*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = sin(313*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_479_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : -sin(pi)/(2*cos(pi/2)) + sin(-pi/2)=2 * sin(-pi/2) * cos(0):=
begin
have : sin(-pi / 2) - sin(pi) / (2 * cos(pi / 2)) = -sin(pi)/(2*cos(pi/2)) + sin(-pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(pi) / ( 2 * cos(pi/2) ),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) - sin(pi/2) = 2 * sin(-pi/2) * cos(0),
{
rw sin_sub_sin,
have : cos(((-pi/2) + (pi/2))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (pi/2))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_481_test (h0 : cos(pi/3)≠ 0) : -sin(395*pi/3)=sin(2*pi/3) / ( 2 * cos(pi/3) ):=
begin
have : sin(pi/3) = -sin(395*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(2*pi/3) / ( 2 * cos(pi/3) ),
{
have : sin(2*pi/3) = sin(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
rw this,
end


lemma Trigo_482_test (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : sin(pi/3)*cos(pi)/(2*cos(pi/6))=- sin(5*pi/6) / 2 + sin(7*pi/6) / 2:=
begin
have : sin(pi / 3) / (2 * cos(pi / 6)) * cos(pi) = sin(pi/3)*cos(pi)/(2*cos(pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(pi/3) / ( 2 * cos(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(pi) = - sin(5*pi/6) / 2 + sin(7*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi) + (pi/6)) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/6)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_483_test (h0 : sin(-pi/3)≠ 0) (h1 : (2*sin(-pi/3))≠ 0) : sin(-2*pi/3)*sin(-pi/6)/(2*sin(-pi/3))=sin(pi/6) / 2 + sin(-pi/2) / 2:=
begin
have : sin(-pi / 6) * (sin((-2) * pi / 3) / (2 * sin(-pi / 3))) = sin(-2*pi/3)*sin(-pi/6)/(2*sin(-pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(-2*pi/3) / ( 2 * sin(-pi/3) ),
{
have : sin(-2*pi/3) = sin(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(-pi/3) = sin(pi/6) / 2 + sin(-pi/2) / 2,
{
rw sin_mul_cos,
have : sin((-pi/6) + (-pi/3)) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (-pi/3)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_484_test : sin(-13*pi/6)*sin(-pi/6) + cos(-13*pi/6)*cos(-pi/6)=cos(50*pi):=
begin
have : sin((-13) * pi / 6) * sin(-pi / 6) + cos((-13) * pi / 6) * cos(-pi / 6) = sin(-13*pi/6)*sin(-pi/6) + cos(-13*pi/6)*cos(-pi/6),
{
field_simp at *,
},
have : cos(-2*pi) = sin(-13*pi/6) * sin(-pi/6) + cos(-13*pi/6) * cos(-pi/6),
{
have : cos(-2*pi) = cos((-13*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(50*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_485_test : 1 - 2*sin(5*pi/12)**2=sin(pi) * sin(pi/6) + cos(pi) * cos(pi/6):=
begin
have : cos(5*pi/6) = 1 - 2 * sin(5*pi/12) ** 2,
{
have : cos(5*pi/6) = cos(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = sin(pi) * sin(pi/6) + cos(pi) * cos(pi/6),
{
have : cos(5*pi/6) = cos((pi) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_486_test : -cos(887*pi/6)=sin(473*pi/3):=
begin
have : sin(-pi/3) = -cos(887*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(473*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_487_test : -sin(-pi/3)*cos(2*pi/3) + sin(2*pi/3)*cos(-pi/3)=cos(37*pi/2):=
begin
have : sin(2 * pi / 3) * cos(-pi / 3) - sin(-pi / 3) * cos(2 * pi / 3) = -sin(-pi/3)*cos(2*pi/3) + sin(2*pi/3)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(2*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(2*pi/3),
{
have : sin(pi) = sin((2*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(37*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_489_test : -1 + 2*cos(pi)**2=- sin(311*pi/2):=
begin
have : 2 * cos(pi) ** 2 - 1 = -1 + 2*cos(pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 2 * cos(pi) ** 2 - 1,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - sin(311*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_490_test : sin(-4*pi)=-2*sin(-2*pi)*cos(151*pi):=
begin
have : 2 * sin((-2) * pi) * -cos(151 * pi) = -2*sin(-2*pi)*cos(151*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -cos(151*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-4*pi) = 2 * sin(-2*pi) * cos(-2*pi),
{
have : sin(-4*pi) = sin(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_491_test : -sin(pi/12)**2 + cos(pi/12)**2=sin(205*pi/3):=
begin
have : cos(pi/6) = -sin(pi/12) ** 2 + cos(pi/12) ** 2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(205*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_492_test : -4*sin(pi/3)**3 + 3*sin(pi/3)=sin(142*pi):=
begin
have : (-4) * sin(pi / 3) ** 3 + 3 * sin(pi / 3) = -4*sin(pi/3)**3 + 3*sin(pi/3),
{
field_simp at *,
},
have : sin(pi) = -4 * sin(pi/3) ** 3 + 3 * sin(pi/3),
{
have : sin(pi) = sin(3*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(142*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_493_test : sin(943*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = sin(943*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_494_test : cos(pi/3)=cos(541*pi/3):=
begin
have : sin(629*pi/6) = cos(541*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (629*pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(629*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_495_test (h0 : cos((-2*pi/3)/2)≠ 0) (h1 : (cos(-2*pi/3)+1)≠ 0) (h2 : (1+cos((-2)*pi/3))≠ 0) : sin(-2*pi/3)/(cos(-2*pi/3) + 1)=- tan(13*pi/3):=
begin
have : sin((-2) * pi / 3) / (1 + cos((-2) * pi / 3)) = sin(-2*pi/3)/(cos(-2*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = sin(-2*pi/3) / ( 1 + cos(-2*pi/3) ),
{
have : tan(-pi/3) = tan((-2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - tan(13*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_497_test : -sin(-2*pi)*cos(359*pi/2)=- sin(3*pi/2) / 2 + sin(-5*pi/2) / 2:=
begin
have : sin((-2) * pi) * -cos(359 * pi / 2) = -sin(-2*pi)*cos(359*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -cos(359*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/2) = - sin(3*pi/2) / 2 + sin(-5*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (-2*pi)) = sin(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (-2*pi)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_498_test : cos(-pi/2)=4*sin(95*pi/3)**3 - 3*sin(95*pi/3):=
begin
have : -((-4) * sin(95 * pi / 3) ** 3 + 3 * sin(95 * pi / 3)) = 4*sin(95*pi/3)**3 - 3*sin(95*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(95*pi) = -4 * sin(95*pi/3) ** 3 + 3 * sin(95*pi/3),
{
have : sin(95*pi) = sin(3*(95*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(95*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_499_test : -sin(97*pi)=2 * sin(pi) * cos(pi):=
begin
have : sin(2*pi) = -sin(97*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = 2 * sin(pi) * cos(pi),
{
have : sin(2*pi) = sin(2*(pi)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
end


lemma Trigo_500_test : cos(-2*pi)=-(3*sin(-pi/3) - 4*sin(-pi/3)**3)**2 + cos(-pi)**2:=
begin
have : -((-4) * sin(-pi / 3) ** 3 + 3 * sin(-pi / 3)) ** 2 + cos(-pi) ** 2 = -(3*sin(-pi/3) - 4*sin(-pi/3)**3)**2 + cos(-pi)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = -4 * sin(-pi/3) ** 3 + 3 * sin(-pi/3),
{
have : sin(-pi) = sin(3*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = - sin(-pi) ** 2 + cos(-pi) ** 2,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_501_test : cos(2*pi)=-sin(515*pi/6)*cos(pi/3) + sin(pi/3)*cos(515*pi/6):=
begin
have : -(sin(515 * pi / 6) * cos(pi / 3) - sin(pi / 3) * cos(515 * pi / 6)) = -sin(515*pi/6)*cos(pi/3) + sin(pi/3)*cos(515*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(171*pi/2) = sin(515*pi/6) * cos(pi/3) - sin(pi/3) * cos(515*pi/6),
{
have : sin(171*pi/2) = sin((515*pi/6) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(171*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_502_test : -sin(1133*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = -sin(1133*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_503_test : cos(77*pi/3)=1 / 2:=
begin
have : sin(pi/6) = cos(77*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_504_test : -cos(2*pi)*cos(320*pi/3)=sin(-11*pi/6) / 2 + sin(13*pi/6) / 2:=
begin
have : -cos(320 * pi / 3) * cos(2 * pi) = -cos(2*pi)*cos(320*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(320*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(2*pi) = sin(-11*pi/6) / 2 + sin(13*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/6) + (2*pi)) = sin(13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (2*pi)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_506_test : -sin(2*pi)*sin(137*pi/2)=- sin(-3*pi) / 2 + sin(pi) / 2:=
begin
have : sin(2 * pi) * -sin(137 * pi / 2) = -sin(2*pi)*sin(137*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(137*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(-pi) = - sin(-3*pi) / 2 + sin(pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi) + (2*pi)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (2*pi)) = sin(-3*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end






lemma Trigo_509_test : 1 - 2*sin(-pi/12)**2=- sin(527*pi/3):=
begin
have : cos(-pi/6) = 1 - 2 * sin(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - sin(527*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_510_test : cos(-pi) + cos(221*pi/2)=- 2 * sin(-3*pi/4) * sin(-pi/4):=
begin
have : cos(-pi) - -cos(221 * pi / 2) = cos(-pi) + cos(221*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(221*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) - cos(pi/2) = - 2 * sin(-3*pi/4) * sin(-pi/4),
{
rw cos_sub_cos,
have : sin(((-pi) + (pi/2))/2) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (pi/2))/2) = sin(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_511_test : (-sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi))*cos(-pi/3)=- sin(-4*pi/3) / 2 + sin(2*pi/3) / 2:=
begin
have : (sin(3 * pi) * cos(2 * pi) - sin(2 * pi) * cos(3 * pi)) * cos(-pi / 3) = (-sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi))*cos(-pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(3*pi) * cos(2*pi) - sin(2*pi) * cos(3*pi),
{
have : sin(pi) = sin((3*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(-pi/3) = - sin(-4*pi/3) / 2 + sin(2*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/3) + (pi)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/3) - (pi)) = sin(-4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_512_test : cos(73*pi)=- sin(21*pi/2):=
begin
have : sin(-pi/2) = cos(73*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(21*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_513_test : cos(71*pi)=- 4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6):=
begin
have : sin(-pi/2) = cos(71*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - 4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_514_test : -cos(179*pi)=- sin(367*pi/2):=
begin
have : sin(pi/2) = -cos(179*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(367*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_516_test : cos(997*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = cos(997*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end






lemma Trigo_519_test : -sin(350*pi/3)=sin(pi/3) * cos(pi) - sin(pi) * cos(pi/3):=
begin
have : sin(-2*pi/3) = -sin(350*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi/3) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = sin(pi/3) * cos(pi) - sin(pi) * cos(pi/3),
{
have : sin(-2*pi/3) = sin((pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end




lemma Trigo_521_test : cos(359*pi/2)**2=1 - cos(-2*pi) ** 2:=
begin
have : sin(-2*pi) = cos(359*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) ** 2 = 1 - cos(-2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_522_test : sin(-pi/6)*sin(pi/6) + cos(-pi/6)*cos(pi/6)=sin(1145*pi/6):=
begin
have : cos(-pi/3) = sin(-pi/6) * sin(pi/6) + cos(-pi/6) * cos(pi/6),
{
have : cos(-pi/3) = cos((-pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(1145*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_523_test : sin(114*pi)=- sin(186*pi):=
begin
have : sin(-2*pi) = sin(114*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(186*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_526_test : sin(-3*pi)*cos(-2*pi) - sin(-2*pi)*cos(-3*pi)=- sin(43*pi):=
begin
have : sin((-3) * pi) * cos((-2) * pi) - sin((-2) * pi) * cos((-3) * pi) = sin(-3*pi)*cos(-2*pi) - sin(-2*pi)*cos(-3*pi),
{
field_simp at *,
},
have : sin(-pi) = sin(-3*pi) * cos(-2*pi) - sin(-2*pi) * cos(-3*pi),
{
have : sin(-pi) = sin((-3*pi) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(43*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_527_test : -sin(687*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -sin(687*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3*pi/4) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_528_test : -3*cos(-pi/9) + 4*cos(-pi/9)**3=- sin(1051*pi/6):=
begin
have : 4 * cos(-pi / 9) ** 3 - 3 * cos(-pi / 9) = -3*cos(-pi/9) + 4*cos(-pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = 4 * cos(-pi/9) ** 3 - 3 * cos(-pi/9),
{
have : cos(-pi/3) = cos(3*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - sin(1051*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_529_test (h0 : tan(41*pi/2)≠ 0) : -1/tan(41*pi/2)=0:=
begin
have : (-1) / tan(41 * pi / 2) = -1/tan(41*pi/2),
{
field_simp at *,
},
have : tan(pi) = -1 / tan(41*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_530_test : -cos(727*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -cos(727*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_531_test : -cos(284*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(284*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_532_test : -sin(394*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -sin(394*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_533_test : sin(158*pi)=0:=
begin
have : sin(pi) = sin(158*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_534_test : -sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi)=0:=
begin
have : sin(3 * pi) * cos(2 * pi) - sin(2 * pi) * cos(3 * pi) = -sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(3*pi) * cos(2*pi) - sin(2*pi) * cos(3*pi),
{
have : sin(pi) = sin((3*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_535_test : -sin(181*pi/2)=- 1:=
begin
have : cos(pi) = -sin(181*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_536_test (h0 : cos(pi)≠ 0) : -cos(313*pi/2)=sin(2*pi) / ( 2 * cos(pi) ):=
begin
have : sin(pi) = -cos(313*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(2*pi) / ( 2 * cos(pi) ),
{
have : sin(2*pi) = sin(2*(pi)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
field_simp at *,
},
rw this,
end




lemma Trigo_538_test : -sin(145*pi)=sin(127*pi):=
begin
have : sin(pi) = -sin(145*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(127*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_539_test : cos(437*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = cos(437*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (3*pi/4) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_540_test : -sin(4*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -sin(4*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_541_test : cos(173*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = cos(173*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_542_test (h0 : cos(pi/6)≠ 0) : sin(pi/6)/cos(pi/6)=- tan(413*pi/6):=
begin
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = - tan(413*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_543_test (h0 : cos(-2*pi/3)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan((-2)*pi/3)*tan(-pi/2))≠ 0) (h3 : (tan(-2*pi/3)*tan(-pi/2)+1)≠ 0) : (tan(-2*pi/3) - tan(-pi/2))/(tan(-2*pi/3)*tan(-pi/2) + 1)=- 1 / tan(52*pi/3):=
begin
have : (tan((-2) * pi / 3) - tan(-pi / 2)) / (1 + tan((-2) * pi / 3) * tan(-pi / 2)) = (tan(-2*pi/3) - tan(-pi/2))/(tan(-2*pi/3)*tan(-pi/2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = ( tan(-2*pi/3) - tan(-pi/2) ) / ( 1 + tan(-2*pi/3) * tan(-pi/2) ),
{
have : tan(-pi/6) = tan((-2*pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - 1 / tan(52*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_545_test : cos(209*pi/2)**2=cos(pi) / 2 + 1 / 2:=
begin
have : cos(pi/2) = cos(209*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) ** 2 = cos(pi) / 2 + 1 / 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end




lemma Trigo_547_test : -tan(253*pi/3)=1 / tan(287*pi/6):=
begin
have : tan(-pi/3) = -tan(253*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = 1 / tan(287*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_548_test : sin(350*pi/3)=cos(575*pi/6):=
begin
have : cos(-pi/6) = sin(350*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(575*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_549_test : sin(2*pi) - sin(-pi/6)=2*sin(13*pi/12)*sin(979*pi/12):=
begin
have : cos(11*pi/12) = sin(979*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/12) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) - sin(-pi/6) = 2 * sin(13*pi/12) * cos(11*pi/12),
{
rw sin_sub_sin,
have : cos(((2*pi) + (-pi/6))/2) = cos(11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi) - (-pi/6))/2) = sin(13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_550_test : -sin(53*pi)=- sin(153*pi):=
begin
have : cos(-pi/2) = -sin(53*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - sin(153*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_551_test : (cos(-pi/3)*cos(5*pi/3) + sin(-pi/3)*sin(5*pi/3))*cos(pi/3)=cos(-5*pi/3) / 2 + cos(7*pi/3) / 2:=
begin
have : cos(pi / 3) * (sin(5 * pi / 3) * sin(-pi / 3) + cos(5 * pi / 3) * cos(-pi / 3)) = (cos(-pi/3)*cos(5*pi/3) + sin(-pi/3)*sin(5*pi/3))*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(5*pi/3) * sin(-pi/3) + cos(5*pi/3) * cos(-pi/3),
{
have : cos(2*pi) = cos((5*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) * cos(2*pi) = cos(-5*pi/3) / 2 + cos(7*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((pi/3) + (2*pi)) = cos(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (2*pi)) = cos(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_552_test : -cos(857*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -cos(857*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_553_test : -sin(-pi/2)*sin(202*pi/3)=- sin(2*pi/3) / 2 + sin(-pi/3) / 2:=
begin
have : sin(-pi / 2) * -sin(202 * pi / 3) = -sin(-pi/2)*sin(202*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(202*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(pi/6) = - sin(2*pi/3) / 2 + sin(-pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/6) + (-pi/2)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (-pi/2)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_554_test : sin(4*pi)=2*sin(2*pi)*sin(313*pi/2):=
begin
have : cos(2*pi) = sin(313*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(4*pi) = 2 * sin(2*pi) * cos(2*pi),
{
have : sin(4*pi) = sin(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_555_test : -tan(128*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(128*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_556_test : cos(481*pi/3)=1 / 2:=
begin
have : sin(5*pi/6) = cos(481*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_557_test (h0 : sin(-pi/3)≠ 0) (h1 : (2*sin(-pi/3))≠ 0) : sin(-2*pi/3)/(2*sin(-pi/3))=cos(445*pi/3):=
begin
have : sin((-2) * pi / 3) / (2 * sin(-pi / 3)) = sin(-2*pi/3)/(2*sin(-pi/3)),
{
field_simp at *,
},
have : cos(-pi/3) = sin(-2*pi/3) / ( 2 * sin(-pi/3) ),
{
have : sin(-2*pi/3) = sin(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(445*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_558_test : cos(2*pi)=sin(65*pi/2):=
begin
have : - -sin(65 * pi / 2) = sin(65*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(19*pi/2) = -sin(65*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (19*pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(19*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_559_test : -sin(-2*pi)*sin(7*pi/3) + cos(-2*pi)*cos(7*pi/3)=1 / 2:=
begin
have : -sin(7 * pi / 3) * sin((-2) * pi) + cos(7 * pi / 3) * cos((-2) * pi) = -sin(-2*pi)*sin(7*pi/3) + cos(-2*pi)*cos(7*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(7*pi/3) * sin(-2*pi) + cos(7*pi/3) * cos(-2*pi),
{
have : cos(pi/3) = cos((7*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_560_test : sin(-pi/3) * sin(pi/2)=cos(-5*pi/6)/2 + cos(1145*pi/6)/2:=
begin
have : cos((-5) * pi / 6) / 2 - -cos(1145 * pi / 6) / 2 = cos(-5*pi/6)/2 + cos(1145*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -cos(1145*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) * sin(pi/2) = cos(-5*pi/6) / 2 - cos(pi/6) / 2,
{
rw sin_mul_sin,
have : cos((-pi/3) + (pi/2)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/3) - (pi/2)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end






lemma Trigo_563_test : sin(979*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = sin(979*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_564_test : -cos(-pi/3)*cos(63*pi/2)=sin(-2*pi/3) / 2 + sin(-4*pi/3) / 2:=
begin
have : -cos(63 * pi / 2) * cos(-pi / 3) = -cos(-pi/3)*cos(63*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(63*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * cos(-pi/3) = sin(-2*pi/3) / 2 + sin(-4*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((-pi) + (-pi/3)) = sin(-4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (-pi/3)) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_566_test : -cos(79*pi)=cos(160*pi):=
begin
have : cos(-2*pi) = -cos(79*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(160*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_567_test : cos(-pi) - cos(pi)=-2*(-sin(-pi/3)*cos(-4*pi/3) + sin(-4*pi/3)*cos(-pi/3))*sin(0):=
begin
have : (-2) * (sin((-4) * pi / 3) * cos(-pi / 3) - sin(-pi / 3) * cos((-4) * pi / 3)) * sin(0) = -2*(-sin(-pi/3)*cos(-4*pi/3) + sin(-4*pi/3)*cos(-pi/3))*sin(0),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = sin(-4*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(-4*pi/3),
{
have : sin(-pi) = sin((-4*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) - cos(pi) = - 2 * sin(-pi) * sin(0),
{
rw cos_sub_cos,
have : sin(((-pi) + (pi))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (pi))/2) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_568_test : cos(-pi/3)=-cos(154*pi/3):=
begin
have : sin(523*pi/6) = cos(154*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (523*pi/6) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(523*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_569_test : sin(2*pi)**2 + (-sin(pi)**2 + cos(pi)**2)**2=1:=
begin
have : cos(2*pi) = -sin(pi) ** 2 + cos(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) ** 2 + cos(2*pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_570_test (h0 : cos(2*pi)≠ 0) : (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))/cos(2*pi)=tan(2*pi):=
begin
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) / cos(2 * pi) = (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))/cos(2*pi),
{
field_simp at *,
},
have : sin(2*pi) = -4 * sin(2*pi/3) ** 3 + 3 * sin(2*pi/3),
{
have : sin(2*pi) = sin(3*(2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) / cos(2*pi) = tan(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_571_test (h0 : tan(397*pi/6)≠ 0) : -1/tan(397*pi/6)=- sqrt( 3 ):=
begin
have : (-1) / tan(397 * pi / 6) = -1/tan(397*pi/6),
{
field_simp at *,
},
have : tan(2*pi/3) = -1 / tan(397*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi/3) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_572_test : sin(-pi/3) / cos(-pi/3)=-tan(250*pi/3):=
begin
have : tan(-pi/3) = -tan(250*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_573_test (h0 : cos((-2)*pi)≠ 0) (h1 : cos(-2*pi)≠ 0) : tan(-2*pi)=cos(145*pi/2)/cos(-2*pi):=
begin
have : cos(145 * pi / 2) / cos((-2) * pi) = cos(145*pi/2)/cos(-2*pi),
{
field_simp at *,
},
have : sin(-2*pi) = cos(145*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_574_test : cos(pi/2)=-cos(-65*pi/2):=
begin
have : -cos((-65) * pi / 2) = -cos(-65*pi/2),
{
field_simp at *,
},
have : sin(50*pi) = -cos(-65*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (50*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(50*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_575_test : sin(-5*pi/6)=sin(-pi/2)*cos(-pi/3) + sin(-pi/3)*cos(367*pi/2):=
begin
have : sin(-pi / 3) * cos(367 * pi / 2) + sin(-pi / 2) * cos(-pi / 3) = sin(-pi/2)*cos(-pi/3) + sin(-pi/3)*cos(367*pi/2),
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = cos(367*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/6) = sin(-pi/3) * cos(-pi/2) + sin(-pi/2) * cos(-pi/3),
{
have : sin(-5*pi/6) = sin((-pi/3) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_576_test : cos(635*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = cos(635*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/4) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_577_test (h0 : tan(1135*pi/12)≠ 0) : -1/tan(1135*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / tan(1135 * pi / 12) = -1/tan(1135*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(1135*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end






lemma Trigo_580_test : sin(2*pi/3)=-2*sin(pi/3)*cos(68*pi/3):=
begin
have : 2 * sin(pi / 3) * -cos(68 * pi / 3) = -2*sin(pi/3)*cos(68*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(68*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) = 2 * sin(pi/3) * cos(pi/3),
{
have : sin(2*pi/3) = sin(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end






lemma Trigo_583_test : sin(-2*pi) * sin(pi/6)=-1/2 - cos(-11*pi/6)/2 + cos(-13*pi/12)**2:=
begin
have : (2 * cos((-13) * pi / 12) ** 2 - 1) / 2 - cos((-11) * pi / 6) / 2 = -1/2 - cos(-11*pi/6)/2 + cos(-13*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-13*pi/6) = 2 * cos(-13*pi/12) ** 2 - 1,
{
have : cos(-13*pi/6) = cos(2*(-13*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * sin(pi/6) = cos(-13*pi/6) / 2 - cos(-11*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((-2*pi) + (pi/6)) = cos(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/6)) = cos(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_585_test : -sin(169*pi/2)=- 4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6):=
begin
have : sin(-pi/2) = -sin(169*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - 4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_586_test : -sin(pi/6)*cos(2*pi/3) + sin(2*pi/3)*cos(pi/6)=1:=
begin
have : sin(2 * pi / 3) * cos(pi / 6) - sin(pi / 6) * cos(2 * pi / 3) = -sin(pi/6)*cos(2*pi/3) + sin(2*pi/3)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(2*pi/3) * cos(pi/6) - sin(pi/6) * cos(2*pi/3),
{
have : sin(pi/2) = sin((2*pi/3) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_587_test : tan(107*pi/3)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = tan(107*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (2*pi/3) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_588_test : 1 - 2*sin(-pi/4)**2=- cos(63*pi/2):=
begin
have : cos(-pi/2) = 1 - 2 * sin(-pi/4) ** 2,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(63*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_589_test : -cos(29*pi)=- cos(15*pi):=
begin
have : cos(-2*pi) = -cos(29*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - cos(15*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_590_test : cos(pi/6)*cos(7*pi/6) + sin(pi/6)*sin(7*pi/6)=- sin(129*pi/2):=
begin
have : sin(7 * pi / 6) * sin(pi / 6) + cos(7 * pi / 6) * cos(pi / 6) = cos(pi/6)*cos(7*pi/6) + sin(pi/6)*sin(7*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(7*pi/6) * sin(pi/6) + cos(7*pi/6) * cos(pi/6),
{
have : cos(pi) = cos((7*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - sin(129*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_592_test : cos(-pi/6) ** 2=1 - sin(235*pi/6)**2:=
begin
have : sin(-pi/6) = sin(235*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) ** 2 = 1 - sin(-pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_593_test (h0 : cos(0)≠ 0) (h1 : cos(pi)≠ 0) (h2 : (1+tan(0)*tan(pi))≠ 0) (h3 : (tan(0)*tan(pi)+1)≠ 0) : (tan(0) - tan(pi))/(tan(0)*tan(pi) + 1)=- tan(9*pi):=
begin
have : (tan(0) - tan(pi)) / (1 + tan(0) * tan(pi)) = (tan(0) - tan(pi))/(tan(0)*tan(pi) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = ( tan(0) - tan(pi) ) / ( 1 + tan(0) * tan(pi) ),
{
have : tan(-pi) = tan((0) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - tan(9*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_595_test : cos(pi/3)=-8*sin(pi/12)**2*cos(pi/12)**2 + 1:=
begin
have : 1 - 2 * (2 * sin(pi / 12) * cos(pi / 12)) ** 2 = -8*sin(pi/12)**2*cos(pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = 2 * sin(pi/12) * cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_596_test : cos(373*pi/2)=- sin(195*pi):=
begin
have : cos(pi/2) = cos(373*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - sin(195*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_597_test : -sin(118*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -sin(118*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end




lemma Trigo_599_test : sin(pi/3) ** 2=1 - sin(899*pi/6)**2:=
begin
have : 1 - (-sin(899 * pi / 6)) ** 2 = 1 - sin(899*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -sin(899*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) ** 2 = 1 - cos(pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_600_test : (1 - 2*sin(pi/6)**2)*cos(pi/2)=cos(pi/6) / 2 + cos(5*pi/6) / 2:=
begin
have : cos(pi / 2) * (1 - 2 * sin(pi / 6) ** 2) = (1 - 2*sin(pi/6)**2)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) * cos(pi/3) = cos(pi/6) / 2 + cos(5*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((pi/2) + (pi/3)) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (pi/3)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_601_test : -cos(487*pi/3)=- sin(pi) * sin(pi/3) + cos(pi) * cos(pi/3):=
begin
have : cos(4*pi/3) = -cos(487*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (4*pi/3) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/3) = - sin(pi) * sin(pi/3) + cos(pi) * cos(pi/3),
{
have : cos(4*pi/3) = cos((pi) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_602_test : cos(7*pi/3)=sin(-2*pi)*sin(115*pi/3) + cos(-2*pi)*cos(pi/3):=
begin
have : sin(115 * pi / 3) * sin((-2) * pi) + cos(pi / 3) * cos((-2) * pi) = sin(-2*pi)*sin(115*pi/3) + cos(-2*pi)*cos(pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = sin(115*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/3) = sin(pi/3) * sin(-2*pi) + cos(pi/3) * cos(-2*pi),
{
have : cos(7*pi/3) = cos((pi/3) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_603_test : cos(4*pi)=-cos(225*pi/2)**2 + cos(2*pi)**2:=
begin
have : sin(2*pi) = cos(225*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi) = - sin(2*pi) ** 2 + cos(2*pi) ** 2,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_604_test : -tan(113*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(113*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_605_test : -sin(-pi/6) + sin(445*pi/6)=2 * sin(pi/6) * cos(0):=
begin
have : sin(445 * pi / 6) - sin(-pi / 6) = -sin(-pi/6) + sin(445*pi/6),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(445*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) - sin(-pi/6) = 2 * sin(pi/6) * cos(0),
{
rw sin_sub_sin,
have : cos(((pi/6) + (-pi/6))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (-pi/6))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_606_test : cos(-2*pi)=-cos(123*pi):=
begin
have : sin(151*pi/2) = cos(123*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (151*pi/2) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = - sin(151*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_608_test : cos(-pi/2) ** 2=1 - sin(139*pi/2)**2:=
begin
have : sin(-pi/2) = sin(139*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) ** 2 = 1 - sin(-pi/2) ** 2,
{
rw cos_sq',
},
rw this,
end




lemma Trigo_610_test (h0 : tan(253*pi/6)≠ 0) : 1/tan(253*pi/6)=1 / tan(295*pi/6):=
begin
have : tan(pi/3) = 1 / tan(253*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(295*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_612_test : cos(721*pi/6)**2=1 - sin(pi/6) ** 2:=
begin
have : cos(pi/6) = cos(721*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) ** 2 = 1 - sin(pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_613_test : 1 - 2*sin(-pi/2)**2=- sin(125*pi/2):=
begin
have : cos(-pi) = 1 - 2 * sin(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(125*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_614_test : cos(170*pi/3)**2=cos(-2*pi/3) / 2 + 1 / 2:=
begin
have : (-cos(170 * pi / 3)) ** 2 = cos(170*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(170*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) ** 2 = cos(-2*pi/3) / 2 + 1 / 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_615_test : sin(2*pi/3)=2*(-3*cos(pi/9) + 4*cos(pi/9)**3)*sin(pi/3):=
begin
have : 2 * sin(pi / 3) * (4 * cos(pi / 9) ** 3 - 3 * cos(pi / 9)) = 2*(-3*cos(pi/9) + 4*cos(pi/9)**3)*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = 4 * cos(pi/9) ** 3 - 3 * cos(pi/9),
{
have : cos(pi/3) = cos(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) = 2 * sin(pi/3) * cos(pi/3),
{
have : sin(2*pi/3) = sin(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_616_test : -sin(226*pi/3) + cos(pi/6)=2 * cos(-pi/6) * cos(0):=
begin
have : cos(-pi/6) = -sin(226*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) + cos(pi/6) = 2 * cos(-pi/6) * cos(0),
{
rw cos_add_cos,
have : cos(((-pi/6) + (pi/6))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (pi/6))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_617_test : cos(151*pi)**2=cos(-4*pi) / 2 + 1 / 2:=
begin
have : (-cos(151 * pi)) ** 2 = cos(151*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(151*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) ** 2 = cos(-4*pi) / 2 + 1 / 2,
{
have : cos(-4*pi) = cos(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_618_test : cos(146*pi)=4 * cos(2*pi) ** 3 - 3 * cos(2*pi):=
begin
have : cos(6*pi) = cos(146*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (6*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(6*pi) = 4 * cos(2*pi) ** 3 - 3 * cos(2*pi),
{
have : cos(6*pi) = cos(3*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_619_test : -sin(-2*pi/3)*cos(-pi) + sin(-pi) + sin(-pi)*cos(-2*pi/3)=2 * sin(-2*pi/3) * cos(-pi/3):=
begin
have : sin(-pi) - (sin((-2) * pi / 3) * cos(-pi) - sin(-pi) * cos((-2) * pi / 3)) = -sin(-2*pi/3)*cos(-pi) + sin(-pi) + sin(-pi)*cos(-2*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(-2*pi/3) * cos(-pi) - sin(-pi) * cos(-2*pi/3),
{
have : sin(pi/3) = sin((-2*pi/3) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) - sin(pi/3) = 2 * sin(-2*pi/3) * cos(-pi/3),
{
rw sin_sub_sin,
have : cos(((-pi) + (pi/3))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (pi/3))/2) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_621_test (h0 : cos(7*pi/3)≠ 0) (h1 : cos(pi/3)≠ 0) (h2 : (1+tan(7*pi/3)*tan(pi/3))≠ 0) (h3 : (1+tan(pi/3)*tan(7*pi/3))≠ 0) : (-tan(pi/3) + tan(7*pi/3))/(1 + tan(pi/3)*tan(7*pi/3))=- tan(62*pi):=
begin
have : (tan(7 * pi / 3) - tan(pi / 3)) / (1 + tan(7 * pi / 3) * tan(pi / 3)) = (-tan(pi/3) + tan(7*pi/3))/(1 + tan(pi/3)*tan(7*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = ( tan(7*pi/3) - tan(pi/3) ) / ( 1 + tan(7*pi/3) * tan(pi/3) ),
{
have : tan(2*pi) = tan((7*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - tan(62*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_622_test (h0 : tan(517*pi/6)≠ 0) : 1/tan(517*pi/6)=sqrt( 3 ):=
begin
have : tan(pi/3) = 1 / tan(517*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_623_test : -cos(507*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -cos(507*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_624_test (h0 : tan(85*pi/4)≠ 0) : 1/tan(85*pi/4)=1:=
begin
have : tan(pi/4) = 1 / tan(85*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_625_test : sin(-2*pi) + sin(2*pi)=2*sin(0)*sin(197*pi/2):=
begin
have : cos(-2*pi) = sin(197*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) + sin(2*pi) = 2 * sin(0) * cos(-2*pi),
{
rw sin_add_sin,
have : sin(((-2*pi) + (2*pi))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (2*pi))/2) = cos(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_626_test : -sin(pi/12)**2 + cos(pi/12)**2=sin(-pi/3) * sin(-pi/2) + cos(-pi/3) * cos(-pi/2):=
begin
have : cos(pi/6) = -sin(pi/12) ** 2 + cos(pi/12) ** 2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(-pi/3) * sin(-pi/2) + cos(-pi/3) * cos(-pi/2),
{
have : cos(pi/6) = cos((-pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_627_test : cos(-pi/3)=-sin(227*pi/6):=
begin
have : sin(259*pi/6) = sin(227*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (259*pi/6) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(259*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_628_test : sin(203*pi/2)=4 * cos(pi/3) ** 3 - 3 * cos(pi/3):=
begin
have : cos(pi) = sin(203*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 4 * cos(pi/3) ** 3 - 3 * cos(pi/3),
{
have : cos(pi) = cos(3*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_629_test : cos(-pi/6)=cos(pi/6)*cos(pi/3) - sin(pi/6)*cos(1183*pi/6):=
begin
have : sin(pi / 6) * -cos(1183 * pi / 6) + cos(pi / 6) * cos(pi / 3) = cos(pi/6)*cos(pi/3) - sin(pi/6)*cos(1183*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = -cos(1183*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(pi/6) * sin(pi/3) + cos(pi/6) * cos(pi/3),
{
have : cos(-pi/6) = cos((pi/6) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_630_test : cos(-pi/3)=-cos(-22*pi/3):=
begin
have : -cos((-22) * pi / 3) = -cos(-22*pi/3),
{
field_simp at *,
},
have : sin(101*pi/6) = -cos(-22*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (101*pi/6) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = sin(101*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_631_test : cos(-pi/3) ** 2=cos(-2*pi/3)/2 + 1/2:=
begin
have : 1 - (1 / 2 - cos((-2) * pi / 3) / 2) = cos(-2*pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) ** 2 = 1 / 2 - cos(-2*pi/3) / 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) ** 2 = 1 - sin(-pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_632_test : -sin(170*pi)=sin(147*pi):=
begin
have : sin(2*pi) = -sin(170*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(147*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_633_test : -sin(73*pi)=0:=
begin
have : cos(pi/2) = -sin(73*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_634_test : sin(697*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = sin(697*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end




lemma Trigo_636_test : -tan(467*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(pi/12) = -tan(467*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end




lemma Trigo_638_test : sin(pi)**2 + cos(129*pi)**2=1:=
begin
have : cos(pi) = cos(129*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) ** 2 + cos(pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_639_test : -sin(117*pi)=- cos(219*pi/2):=
begin
have : sin(-2*pi) = -sin(117*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - cos(219*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_640_test : sin(367*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(367*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end




lemma Trigo_642_test (h0 : sin(3*pi/2)≠ 0) (h1 : -sin(3*pi/2)≠ 0) : -sin(2*pi)/sin(3*pi/2)=tan(2*pi):=
begin
have : sin(2 * pi) / -sin(3 * pi / 2) = -sin(2*pi)/sin(3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(3*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) / cos(2*pi) = tan(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_643_test : cos(335*pi/3)=1 / 2:=
begin
have : cos(pi/3) = cos(335*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_644_test : sin(-pi) ** 2=1 - cos(24*pi)**2:=
begin
have : 1 - (-cos(24 * pi)) ** 2 = 1 - cos(24*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -cos(24*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) ** 2 = 1 - cos(-pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_645_test : -cos(58*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(58*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_646_test : -sin(109*pi/2)=sin(295*pi/2):=
begin
have : sin(-pi/2) = -sin(109*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(295*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_647_test : -sin(-pi/4)**2 + cos(-pi/4)**2=sin(77*pi):=
begin
have : cos(-pi/2) = -sin(-pi/4) ** 2 + cos(-pi/4) ** 2,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(77*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_648_test : cos(305*pi/6)=cos(941*pi/6):=
begin
have : sin(-pi/3) = cos(305*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(941*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_650_test : sin(77*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = sin(77*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_651_test (h0 : -cos(153*pi)≠ 0) (h1 : cos(153*pi)≠ 0) : -sin(-2*pi)/cos(153*pi)=tan(-2*pi):=
begin
have : sin((-2) * pi) / -cos(153 * pi) = -sin(-2*pi)/cos(153*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(153*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) / cos(-2*pi) = tan(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_652_test : sin(317*pi/3)=- sin(542*pi/3):=
begin
have : sin(-pi/3) = sin(317*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(542*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_653_test (h0 : cos(-pi/6)≠ 0) (h1 : (2*cos(-pi/6))≠ 0) : sin(-pi/3)/(2*cos(-pi/6)) + sin(pi)=2 * sin(5*pi/12) * cos(7*pi/12):=
begin
have : sin(pi) + sin(-pi / 3) / (2 * cos(-pi / 6)) = sin(-pi/3)/(2*cos(-pi/6)) + sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(-pi/3) / ( 2 * cos(-pi/6) ),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) + sin(-pi/6) = 2 * sin(5*pi/12) * cos(7*pi/12),
{
rw sin_add_sin,
have : sin(((pi) + (-pi/6))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (-pi/6))/2) = cos(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_654_test : cos(2*pi)*cos(311*pi/2)=- sin(4*pi) / 2 + sin(0) / 2:=
begin
have : cos(311 * pi / 2) * cos(2 * pi) = cos(2*pi)*cos(311*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(311*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(2*pi) = - sin(4*pi) / 2 + sin(0) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((2*pi) + (-2*pi)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (-2*pi)) = sin(4*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_655_test : sin(2*pi)*cos(-4*pi) + sin(-4*pi)*cos(2*pi)=sin(18*pi):=
begin
have : sin((-4) * pi) * cos(2 * pi) + sin(2 * pi) * cos((-4) * pi) = sin(2*pi)*cos(-4*pi) + sin(-4*pi)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-4*pi) * cos(2*pi) + sin(2*pi) * cos(-4*pi),
{
have : sin(-2*pi) = sin((-4*pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(18*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_656_test : sin(3*pi)=sin(pi)*cos(2*pi) - sin(2*pi)*cos(44*pi):=
begin
have : sin(pi) * cos(2 * pi) + sin(2 * pi) * -cos(44 * pi) = sin(pi)*cos(2*pi) - sin(2*pi)*cos(44*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -cos(44*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi) = sin(pi) * cos(2*pi) + sin(2*pi) * cos(pi),
{
have : sin(3*pi) = sin((pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end




lemma Trigo_658_test : -sin(-pi)*cos(329*pi/6)=sin(-5*pi/6) / 2 + sin(-7*pi/6) / 2:=
begin
have : sin(-pi) * -cos(329 * pi / 6) = -sin(-pi)*cos(329*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -cos(329*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * cos(-pi/6) = sin(-5*pi/6) / 2 + sin(-7*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-pi) + (-pi/6)) = sin(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (-pi/6)) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_659_test (h0 : sin(7*pi/6)≠ 0) (h1 : (2*sin(7*pi/6))≠ 0) (h2 : (4*sin(7*pi/6))≠ 0) : sin(pi) * sin(pi/6)=cos(5*pi/6)/2 - sin(7*pi/3)/(4*sin(7*pi/6)):=
begin
have : cos(5 * pi / 6) / 2 - sin(7 * pi / 3) / (2 * sin(7 * pi / 6)) / 2 = cos(5*pi/6)/2 - sin(7*pi/3)/(4*sin(7*pi/6)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/6) = sin(7*pi/3) / ( 2 * sin(7*pi/6) ),
{
have : sin(7*pi/3) = sin(2*(7*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * sin(pi/6) = cos(5*pi/6) / 2 - cos(7*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((pi) + (pi/6)) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (pi/6)) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_660_test : -cos(1145*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -cos(1145*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_661_test (h0 : cos(-pi)≠ 0) : cos(267*pi/2)/cos(-pi)=tan(-pi):=
begin
have : sin(-pi) = cos(267*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) / cos(-pi) = tan(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_663_test (h0 : sin(-pi/2)≠ 0) (h1 : (4*sin(-pi/2)**2)≠ 0) (h2 : (2*sin(-pi/2))≠ 0) : sin(-pi)**2/(4*sin(-pi/2)**2)=1 - sin(-pi/2) ** 2:=
begin
have : (sin(-pi) / (2 * sin(-pi / 2))) ** 2 = sin(-pi)**2/(4*sin(-pi/2)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(-pi) / ( 2 * sin(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) ** 2 = 1 - sin(-pi/2) ** 2,
{
rw cos_sq',
},
rw this,
end




lemma Trigo_665_test : -cos(pi/2)*cos(485*pi/6)=cos(2*pi/3) / 2 + cos(pi/3) / 2:=
begin
have : cos(pi / 2) * -cos(485 * pi / 6) = -cos(pi/2)*cos(485*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -cos(485*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) * cos(-pi/6) = cos(2*pi/3) / 2 + cos(pi/3) / 2,
{
rw cos_mul_cos,
have : cos((pi/2) + (-pi/6)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (-pi/6)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_666_test : -sin(63*pi)=cos(331*pi/2):=
begin
have : sin(2*pi) = -sin(63*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(331*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_667_test : sin(2*pi) ** 2=1 - cos(194*pi)**2:=
begin
have : cos(2*pi) = cos(194*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) ** 2 = 1 - cos(2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end






lemma Trigo_670_test : sin(pi) + sin(pi/2)=2*(-3*cos(pi/12) + 4*cos(pi/12)**3)*sin(3*pi/4):=
begin
have : 2 * sin(3 * pi / 4) * (4 * cos(pi / 12) ** 3 - 3 * cos(pi / 12)) = 2*(-3*cos(pi/12) + 4*cos(pi/12)**3)*sin(3*pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = 4 * cos(pi/12) ** 3 - 3 * cos(pi/12),
{
have : cos(pi/4) = cos(3*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi) + sin(pi/2) = 2 * sin(3*pi/4) * cos(pi/4),
{
rw sin_add_sin,
have : sin(((pi) + (pi/2))/2) = sin(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (pi/2))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_671_test : -sin(562*pi/3)=cos(133*pi/6):=
begin
have : cos(pi/6) = -sin(562*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(133*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_673_test : -cos(973*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(973*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end




lemma Trigo_675_test : cos(-pi/3)=sin(421*pi/6):=
begin
have : sin(277*pi/6) = sin(421*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (277*pi/6) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = sin(277*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_677_test : cos(56*pi)=cos(198*pi):=
begin
have : sin(pi/2) = cos(56*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(198*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_678_test (h0 : cos(-pi/2)≠ 0) (h1 : (2*cos(-pi/2))≠ 0) : sin(-pi)/(2*cos(-pi/2)) + sin(pi/3)=2 * sin(-pi/12) * cos(5*pi/12):=
begin
have : sin(pi / 3) + sin(-pi) / (2 * cos(-pi / 2)) = sin(-pi)/(2*cos(-pi/2)) + sin(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-pi) / ( 2 * cos(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) + sin(-pi/2) = 2 * sin(-pi/12) * cos(5*pi/12),
{
rw sin_add_sin,
have : sin(((pi/3) + (-pi/2))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (-pi/2))/2) = cos(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_679_test (h0 : tan(137*pi/2)≠ 0) : 1/tan(137*pi/2)=0:=
begin
have : tan(pi) = 1 / tan(137*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_680_test : sin(171*pi)**2=1 - cos(-2*pi) ** 2:=
begin
have : sin(-2*pi) = sin(171*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) ** 2 = 1 - cos(-2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_681_test : cos(188*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(188*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end




lemma Trigo_683_test : -sin(309*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -sin(309*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_684_test : -sin(-2*pi)*sin(13*pi/6) + cos(-2*pi)*cos(13*pi/6)=sqrt( 3 ) / 2:=
begin
have : -sin(13 * pi / 6) * sin((-2) * pi) + cos(13 * pi / 6) * cos((-2) * pi) = -sin(-2*pi)*sin(13*pi/6) + cos(-2*pi)*cos(13*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(13*pi/6) * sin(-2*pi) + cos(13*pi/6) * cos(-2*pi),
{
have : cos(pi/6) = cos((13*pi/6) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_685_test : -1 + 2*cos(-pi/6)**2=- cos(154*pi/3):=
begin
have : 2 * cos(-pi / 6) ** 2 - 1 = -1 + 2*cos(-pi/6)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = 2 * cos(-pi/6) ** 2 - 1,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(154*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_686_test : sin(129*pi/2)=1:=
begin
have : sin(pi/2) = sin(129*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_687_test (h0 : tan(233*pi/4)≠ 0) : -1/tan(233*pi/4)=- 1:=
begin
have : (-1) / tan(233 * pi / 4) = -1/tan(233*pi/4),
{
field_simp at *,
},
have : tan(3*pi/4) = -1 / tan(233*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (3*pi/4) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_688_test (h0 : tan(25*pi/2)≠ 0) : 1/tan(25*pi/2)=- 1 / tan(15*pi/2):=
begin
have : tan(2*pi) = 1 / tan(25*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - 1 / tan(15*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_689_test : 2*sin(pi)*cos(pi)=sin(152*pi):=
begin
have : sin(2*pi) = 2 * sin(pi) * cos(pi),
{
have : sin(2*pi) = sin(2*(pi)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(152*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_690_test : -sin(143*pi/6)=1 / 2:=
begin
have : sin(pi/6) = -sin(143*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_691_test : sin(-4*pi/3)*cos(pi) + sin(pi)*cos(-4*pi/3)=sin(406*pi/3):=
begin
have : sin((-4) * pi / 3) * cos(pi) + sin(pi) * cos((-4) * pi / 3) = sin(-4*pi/3)*cos(pi) + sin(pi)*cos(-4*pi/3),
{
field_simp at *,
},
have : sin(-pi/3) = sin(-4*pi/3) * cos(pi) + sin(pi) * cos(-4*pi/3),
{
have : sin(-pi/3) = sin((-4*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(406*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_692_test : sin(40*pi)=- cos(217*pi/2):=
begin
have : sin(-2*pi) = sin(40*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - cos(217*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_693_test : -sin(-2*pi)*sin(6*pi) + cos(-2*pi)*cos(6*pi)=1 - 2 * sin(2*pi) ** 2:=
begin
have : -sin(6 * pi) * sin((-2) * pi) + cos(6 * pi) * cos((-2) * pi) = -sin(-2*pi)*sin(6*pi) + cos(-2*pi)*cos(6*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = -sin(6*pi) * sin(-2*pi) + cos(6*pi) * cos(-2*pi),
{
have : cos(4*pi) = cos((6*pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = 1 - 2 * sin(2*pi) ** 2,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end




lemma Trigo_695_test : cos(5*pi/6)*cos(2*pi) + sin(5*pi/6)*sin(2*pi)=- sin(-pi) * sin(-pi/6) + cos(-pi) * cos(-pi/6):=
begin
have : sin(5 * pi / 6) * sin(2 * pi) + cos(5 * pi / 6) * cos(2 * pi) = cos(5*pi/6)*cos(2*pi) + sin(5*pi/6)*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/6) = sin(5*pi/6) * sin(2*pi) + cos(5*pi/6) * cos(2*pi),
{
have : cos(-7*pi/6) = cos((5*pi/6) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/6) = - sin(-pi) * sin(-pi/6) + cos(-pi) * cos(-pi/6),
{
have : cos(-7*pi/6) = cos((-pi) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_696_test : sin(-pi) + sin(-pi/2)=2*(sin(3*pi/4)*sin(pi) + cos(3*pi/4)*cos(pi))*sin(-3*pi/4):=
begin
have : 2 * sin((-3) * pi / 4) * (sin(3 * pi / 4) * sin(pi) + cos(3 * pi / 4) * cos(pi)) = 2*(sin(3*pi/4)*sin(pi) + cos(3*pi/4)*cos(pi))*sin(-3*pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = sin(3*pi/4) * sin(pi) + cos(3*pi/4) * cos(pi),
{
have : cos(-pi/4) = cos((3*pi/4) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) + sin(-pi/2) = 2 * sin(-3*pi/4) * cos(-pi/4),
{
rw sin_add_sin,
have : sin(((-pi) + (-pi/2))/2) = sin(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (-pi/2))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_697_test (h0 : cos(pi/6)≠ 0) : tan(pi/6)=(sin(2*pi/3)*cos(-pi/2) + sin(-pi/2)*cos(2*pi/3))/cos(pi/6):=
begin
have : sin(pi/6) = sin(2*pi/3) * cos(-pi/2) + sin(-pi/2) * cos(2*pi/3),
{
have : sin(pi/6) = sin((2*pi/3) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_698_test : sin(133*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = sin(133*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end




lemma Trigo_700_test (h0 : sin(-pi/2)≠ 0) (h1 : (2*sin(-pi/2))≠ 0) : sin(-pi)/(2*sin(-pi/2)) + cos(pi/6)=2 * cos(-pi/3) * cos(-pi/6):=
begin
have : cos(-pi/2) = sin(-pi) / ( 2 * sin(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) + cos(pi/6) = 2 * cos(-pi/3) * cos(-pi/6),
{
rw cos_add_cos,
have : cos(((-pi/2) + (pi/6))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (pi/6))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_701_test : sin(pi/6)=sin(593*pi/6):=
begin
have : - -sin(593 * pi / 6) = sin(593*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi/3) = -sin(593*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/3) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(4*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_703_test : cos(-2*pi/3)*cos(-pi/2) + sin(-2*pi/3)*sin(-pi/2) + cos(pi/6)=2 * cos(pi/6) * cos(0):=
begin
have : cos(pi / 6) + (sin((-2) * pi / 3) * sin(-pi / 2) + cos((-2) * pi / 3) * cos(-pi / 2)) = cos(-2*pi/3)*cos(-pi/2) + sin(-2*pi/3)*sin(-pi/2) + cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(-2*pi/3) * sin(-pi/2) + cos(-2*pi/3) * cos(-pi/2),
{
have : cos(-pi/6) = cos((-2*pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) + cos(-pi/6) = 2 * cos(pi/6) * cos(0),
{
rw cos_add_cos,
have : cos(((pi/6) + (-pi/6))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/6) - (-pi/6))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_705_test : cos(-5*pi/6)*cos(-pi/6) - sin(-5*pi/6)*sin(-pi/6)=cos(33*pi):=
begin
have : -sin((-5) * pi / 6) * sin(-pi / 6) + cos((-5) * pi / 6) * cos(-pi / 6) = cos(-5*pi/6)*cos(-pi/6) - sin(-5*pi/6)*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(-5*pi/6) * sin(-pi/6) + cos(-5*pi/6) * cos(-pi/6),
{
have : cos(-pi) = cos((-5*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(33*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_706_test : -sin(65*pi/2)=- 1:=
begin
have : cos(pi) = -sin(65*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_707_test : -3*cos(-pi/3) + 4*cos(-pi/3)**3=- cos(186*pi):=
begin
have : 4 * cos(-pi / 3) ** 3 - 3 * cos(-pi / 3) = -3*cos(-pi/3) + 4*cos(-pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = 4 * cos(-pi/3) ** 3 - 3 * cos(-pi/3),
{
have : cos(-pi) = cos(3*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(186*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_708_test : sin(201*pi/2)=sin(73*pi/2):=
begin
have : sin(pi/2) = sin(201*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(73*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_709_test : sin(pi/2)*cos(521*pi/3)=cos(pi/3) / 2 - cos(2*pi/3) / 2:=
begin
have : sin(pi/6) = cos(521*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * sin(pi/6) = cos(pi/3) / 2 - cos(2*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((pi/2) + (pi/6)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (pi/6)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_710_test : 1 - 2*sin(pi/6)**2=- cos(518*pi/3):=
begin
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - cos(518*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_711_test : cos(20*pi)=2 * cos(-pi) ** 2 - 1:=
begin
have : cos(-2*pi) = cos(20*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = 2 * cos(-pi) ** 2 - 1,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_712_test : sin(pi)**2 + cos(35*pi)**2=1:=
begin
have : cos(pi) = cos(35*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) ** 2 + cos(pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_713_test : cos(229*pi/3)=- sin(1111*pi/6):=
begin
have : sin(pi/6) = cos(229*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(1111*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_714_test : cos(4*pi)=1 - 2*sin(11*pi)**2:=
begin
have : sin(2*pi) = sin(11*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi) = 1 - 2 * sin(2*pi) ** 2,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_715_test : cos(-2*pi/3)=-8*sin(-pi/6)**2*cos(-pi/6)**2 + 1:=
begin
have : 1 - 2 * (2 * sin(-pi / 6) * cos(-pi / 6)) ** 2 = -8*sin(-pi/6)**2*cos(-pi/6)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = 2 * sin(-pi/6) * cos(-pi/6),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) = 1 - 2 * sin(-pi/3) ** 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end




lemma Trigo_717_test : 3*sin(-pi/6) - 4*sin(-pi/6)**3=cos(23*pi):=
begin
have : (-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6) = 3*sin(-pi/6) - 4*sin(-pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(23*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_718_test (h0 : cos((-2*pi)/2)≠ 0) (h1 : sin(-2*pi)≠ 0) (h2 : sin((-2)*pi)≠ 0) : (1 - cos(-2*pi))/sin(-2*pi)=tan(39*pi):=
begin
have : (1 - cos((-2) * pi)) / sin((-2) * pi) = (1 - cos(-2*pi))/sin(-2*pi),
{
field_simp at *,
},
have : tan(-pi) = ( 1 - cos(-2*pi) ) / sin(-2*pi),
{
have : tan(-pi) = tan((-2*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(39*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_719_test : cos(-pi/3)*cos(pi/6) - sin(-pi/3)*sin(pi/6)=cos(421*pi/6):=
begin
have : -sin(-pi / 3) * sin(pi / 6) + cos(-pi / 3) * cos(pi / 6) = cos(-pi/3)*cos(pi/6) - sin(-pi/3)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/3) * sin(pi/6) + cos(-pi/3) * cos(pi/6),
{
have : cos(-pi/6) = cos((-pi/3) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(421*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_720_test : -sin(65*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -sin(65*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_721_test (h0 : cos(110*pi/3)≠ 0) (h1 : (2*cos(110*pi/3))≠ 0) : cos(pi/6)=sin(220*pi/3)/(2*cos(110*pi/3)):=
begin
have : sin(110*pi/3) = sin(220*pi/3) / ( 2 * cos(110*pi/3) ),
{
have : sin(220*pi/3) = sin(2*(110*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(110*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_722_test : sin(pi) ** 2=1 - (1 - 2*sin(pi/2)**2)**2:=
begin
have : cos(pi) = 1 - 2 * sin(pi/2) ** 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi) ** 2 = 1 - cos(pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_723_test : -sin(-pi/4)**2 + cos(-pi/4)**2=cos(311*pi/2):=
begin
have : cos(-pi/2) = -sin(-pi/4) ** 2 + cos(-pi/4) ** 2,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(311*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_726_test : cos(pi)=sin(pi/2)*cos(3*pi) + cos(-pi/2)*cos(pi/2):=
begin
have : sin(pi / 2) * cos(3 * pi) + cos(pi / 2) * cos(-pi / 2) = sin(pi/2)*cos(3*pi) + cos(-pi/2)*cos(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = cos(3*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = sin(pi/2) * sin(-pi/2) + cos(pi/2) * cos(-pi/2),
{
have : cos(pi) = cos((pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end




lemma Trigo_728_test : -tan(62*pi)=- 1 / tan(173*pi/2):=
begin
have : tan(2*pi) = -tan(62*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - 1 / tan(173*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_729_test : sin(2*pi) + sin(-2*pi)=-2*sin(0)*cos(185*pi):=
begin
have : 2 * sin(0) * -cos(185 * pi) = -2*sin(0)*cos(185*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -cos(185*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) + sin(-2*pi) = 2 * sin(0) * cos(2*pi),
{
rw sin_add_sin,
have : sin(((2*pi) + (-2*pi))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (-2*pi))/2) = cos(2*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_730_test : sin(123*pi)=cos(181*pi/2):=
begin
have : cos(pi/2) = sin(123*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(181*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_731_test : 2*sin(pi/3)*cos(pi/3)=sin(pi/6) * cos(-pi/2) - sin(-pi/2) * cos(pi/6):=
begin
have : sin(2*pi/3) = 2 * sin(pi/3) * cos(pi/3),
{
have : sin(2*pi/3) = sin(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(pi/6) * cos(-pi/2) - sin(-pi/2) * cos(pi/6),
{
have : sin(2*pi/3) = sin((pi/6) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_732_test : sin(-pi/3)=-cos(pi)*cos(353*pi/6) - sin(pi)*sin(353*pi/6):=
begin
have : -(sin(353 * pi / 6) * sin(pi) + cos(353 * pi / 6) * cos(pi)) = -cos(pi)*cos(353*pi/6) - sin(pi)*sin(353*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(347*pi/6) = sin(353*pi/6) * sin(pi) + cos(353*pi/6) * cos(pi),
{
have : cos(347*pi/6) = cos((353*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = - cos(347*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_734_test : -sin(pi)**2 + cos(pi)**2=- sin(191*pi/2):=
begin
have : cos(2*pi) = -sin(pi) ** 2 + cos(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - sin(191*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_735_test : cos(817*pi/6)=cos(875*pi/6):=
begin
have : cos(pi/6) = cos(817*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(875*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_736_test : -sin(32*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(32*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_737_test : sin(-pi) * cos(-pi/3)=-sin(pi)*cos(-pi/3):=
begin
have : (-1) / 2 * (2 * sin(pi) * cos(-pi / 3)) = -sin(pi)*cos(-pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) - sin(-4*pi/3) = 2 * sin(pi) * cos(-pi/3),
{
rw sin_sub_sin,
have : cos(((2*pi/3) + (-4*pi/3))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi/3) - (-4*pi/3))/2) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -1/2*(sin(2*pi/3) - sin(-4*pi/3)) = -sin(2*pi/3)/2+sin(-4*pi/3)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi) * cos(-pi/3) = - sin(2*pi/3) / 2 + sin(-4*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/3) + (-pi)) = sin(-4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/3) - (-pi)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_738_test : cos(-2*pi/3)=1 - 2*cos(583*pi/6)**2:=
begin
have : sin(-pi/3) = cos(583*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) = 1 - 2 * sin(-pi/3) ** 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end




lemma Trigo_740_test : -tan(33*pi)=0:=
begin
have : tan(pi) = -tan(33*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_741_test : sin(169*pi)=cos(185*pi/2):=
begin
have : cos(-pi/2) = sin(169*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(185*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_742_test : -1 + 2*cos(pi/12)**2=- sin(208*pi/3):=
begin
have : 2 * cos(pi / 12) ** 2 - 1 = -1 + 2*cos(pi/12)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = 2 * cos(pi/12) ** 2 - 1,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - sin(208*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_743_test : cos(-2*pi)=-2*sin(355*pi/4)*cos(355*pi/4):=
begin
have : -(2 * sin(355 * pi / 4) * cos(355 * pi / 4)) = -2*sin(355*pi/4)*cos(355*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(355*pi/2) = 2 * sin(355*pi/4) * cos(355*pi/4),
{
have : sin(355*pi/2) = sin(2*(355*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = - sin(355*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_744_test : cos(-4*pi)=1 - 2*sin(144*pi)**2:=
begin
have : 1 - 2 * (-sin(144 * pi)) ** 2 = 1 - 2*sin(144*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = -sin(144*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi) = 1 - 2 * sin(-2*pi) ** 2,
{
have : cos(-4*pi) = cos(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_745_test : cos(pi/3)*cos(154*pi)=cos(-5*pi/3) / 2 + cos(7*pi/3) / 2:=
begin
have : cos(2*pi) = cos(154*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) * cos(2*pi) = cos(-5*pi/3) / 2 + cos(7*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((pi/3) + (2*pi)) = cos(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (2*pi)) = cos(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_746_test : sin(pi/2)=-1 + 2*sin(139*pi/2)**2:=
begin
have : -(1 - 2 * sin(139 * pi / 2) ** 2) = -1 + 2*sin(139*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(139*pi) = 1 - 2 * sin(139*pi/2) ** 2,
{
have : cos(139*pi) = cos(2*(139*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = - cos(139*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_747_test : cos(-pi/3)=cos(-pi/2)*cos(pi/6) - (3*sin(-pi/6) - 4*sin(-pi/6)**3)*sin(pi/6):=
begin
have : -sin(pi / 6) * ((-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6)) + cos(pi / 6) * cos(-pi / 2) = cos(-pi/2)*cos(pi/6) - (3*sin(-pi/6) - 4*sin(-pi/6)**3)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(pi/6) * sin(-pi/2) + cos(pi/6) * cos(-pi/2),
{
have : cos(-pi/3) = cos((pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_748_test : cos(289*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = cos(289*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_749_test : -sin(-pi)*sin(160*pi)=- sin(3*pi/2) / 2 + sin(-pi/2) / 2:=
begin
have : sin(-pi) * -sin(160 * pi) = -sin(-pi)*sin(160*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(160*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * cos(pi/2) = - sin(3*pi/2) / 2 + sin(-pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/2) + (-pi)) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (-pi)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_750_test : sin(pi)*sin(3*pi/2) + cos(pi)*cos(3*pi/2)=sin(116*pi):=
begin
have : sin(3 * pi / 2) * sin(pi) + cos(3 * pi / 2) * cos(pi) = sin(pi)*sin(3*pi/2) + cos(pi)*cos(3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(3*pi/2) * sin(pi) + cos(3*pi/2) * cos(pi),
{
have : cos(pi/2) = cos((3*pi/2) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(116*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_752_test : cos(-7*pi/3)*cos(-pi/3) + cos(-pi/3) + sin(-7*pi/3)*sin(-pi/3)=2 * cos(-5*pi/6) * cos(-7*pi/6):=
begin
have : sin((-7) * pi / 3) * sin(-pi / 3) + cos((-7) * pi / 3) * cos(-pi / 3) + cos(-pi / 3) = cos(-7*pi/3)*cos(-pi/3) + cos(-pi/3) + sin(-7*pi/3)*sin(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(-7*pi/3) * sin(-pi/3) + cos(-7*pi/3) * cos(-pi/3),
{
have : cos(-2*pi) = cos((-7*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(-pi/3) = 2 * cos(-5*pi/6) * cos(-7*pi/6),
{
rw cos_add_cos,
have : cos(((-2*pi) + (-pi/3))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (-pi/3))/2) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_753_test : cos(2*pi)=-sin(-pi/6)*cos(29*pi/3) - sin(29*pi/3)*cos(-pi/6):=
begin
have : -(sin(29 * pi / 3) * cos(-pi / 6) + sin(-pi / 6) * cos(29 * pi / 3)) = -sin(-pi/6)*cos(29*pi/3) - sin(29*pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(19*pi/2) = sin(29*pi/3) * cos(-pi/6) + sin(-pi/6) * cos(29*pi/3),
{
have : sin(19*pi/2) = sin((29*pi/3) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(19*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_754_test : -cos(473*pi/3)=2 * cos(pi/3) ** 2 - 1:=
begin
have : cos(2*pi/3) = -cos(473*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi/3) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = 2 * cos(pi/3) ** 2 - 1,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_755_test : cos(pi) ** 2=1 - cos(267*pi/2)**2:=
begin
have : 1 - (-cos(267 * pi / 2)) ** 2 = 1 - cos(267*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -cos(267*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) ** 2 = 1 - sin(pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_756_test : sin(2*pi) + sin(-pi/6)=-2*sin(11*pi/12)*sin(2093*pi/12):=
begin
have : 2 * sin(11 * pi / 12) * -sin(2093 * pi / 12) = -2*sin(11*pi/12)*sin(2093*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(13*pi/12) = -sin(2093*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/12) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) + sin(-pi/6) = 2 * sin(11*pi/12) * cos(13*pi/12),
{
rw sin_add_sin,
have : sin(((2*pi) + (-pi/6))/2) = sin(11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (-pi/6))/2) = cos(13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_757_test : cos(pi/2)=-sin(208*pi):=
begin
have : sin(184*pi) = sin(208*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (184*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(184*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_759_test (h0 : cos((-pi)/2)≠ 0) (h1 : sin(-pi)≠ 0) : (1 - cos(-pi))/sin(-pi)=- 1 / tan(3*pi):=
begin
have : tan(-pi/2) = ( 1 - cos(-pi) ) / sin(-pi),
{
have : tan(-pi/2) = tan((-pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - 1 / tan(3*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_760_test : sin(-pi)=-1 + 2*sin(95*pi/4)**2:=
begin
have : -(1 - 2 * sin(95 * pi / 4) ** 2) = -1 + 2*sin(95*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(95*pi/2) = 1 - 2 * sin(95*pi/4) ** 2,
{
have : cos(95*pi/2) = cos(2*(95*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(95*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_761_test : sin(pi)**2 + sin(109*pi/2)**2=1:=
begin
have : sin(pi) ** 2 + (-sin(109 * pi / 2)) ** 2 = sin(pi)**2 + sin(109*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(109*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) ** 2 + cos(pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_762_test : sin(0)=sin(-pi/6)*cos(pi/6) + sin(pi/6)*sin(278*pi/3):=
begin
have : sin(pi / 6) * sin(278 * pi / 3) + sin(-pi / 6) * cos(pi / 6) = sin(-pi/6)*cos(pi/6) + sin(pi/6)*sin(278*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(278*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(0) = sin(pi/6) * cos(-pi/6) + sin(-pi/6) * cos(pi/6),
{
have : sin(0) = sin((pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_763_test : sin(127*pi)=cos(71*pi/2):=
begin
have : cos(-pi/2) = sin(127*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(71*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_764_test : sin(185*pi/2)=- sin(31*pi/2):=
begin
have : sin(pi/2) = sin(185*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(31*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_765_test (h0 : cos(pi/3)≠ 0) : tan(pi/3)=-cos(871*pi/6)/cos(pi/3):=
begin
have : sin(pi/3) = -cos(871*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_766_test : -sin(188*pi)*cos(-pi/3)=sin(-5*pi/3) / 2 + sin(-7*pi/3) / 2:=
begin
have : sin(-2*pi) = -sin(188*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/3) = sin(-5*pi/3) / 2 + sin(-7*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-pi/3)) = sin(-7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-pi/3)) = sin(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_767_test : cos(-pi/3)=cos(583*pi/3):=
begin
have : - -cos(583 * pi / 3) = cos(583*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(251*pi/6) = -cos(583*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (251*pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(251*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_768_test : cos(112*pi)=1:=
begin
have : sin(pi/2) = cos(112*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_769_test : sin(157*pi/2)=cos(34*pi):=
begin
have : sin(pi/2) = sin(157*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(34*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_770_test : sin(pi) - sin(pi/6)=-2*sin(5*pi/12)*sin(131*pi/12):=
begin
have : 2 * sin(5 * pi / 12) * -sin(131 * pi / 12) = -2*sin(5*pi/12)*sin(131*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/12) = -sin(131*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) - sin(pi/6) = 2 * sin(5*pi/12) * cos(7*pi/12),
{
rw sin_sub_sin,
have : cos(((pi) + (pi/6))/2) = cos(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi) - (pi/6))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_772_test : sin(1045*pi/6)=sin(1061*pi/6):=
begin
have : sin(pi/6) = sin(1045*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(1061*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_773_test : sin(125*pi/3) + sin(2*pi)=2 * sin(5*pi/6) * cos(-7*pi/6):=
begin
have : sin(-pi/3) = sin(125*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) + sin(2*pi) = 2 * sin(5*pi/6) * cos(-7*pi/6),
{
rw sin_add_sin,
have : sin(((-pi/3) + (2*pi))/2) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (2*pi))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_774_test : sin(211*pi/3)*cos(-pi/2)=sin(5*pi/6) / 2 + sin(-pi/6) / 2:=
begin
have : sin(pi/3) = sin(211*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(-pi/2) = sin(5*pi/6) / 2 + sin(-pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (-pi/2)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/2)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_775_test : -cos(481*pi/6)=sin(pi/2) * sin(-pi/3) + cos(pi/2) * cos(-pi/3):=
begin
have : cos(5*pi/6) = -cos(481*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = sin(pi/2) * sin(-pi/3) + cos(pi/2) * cos(-pi/3),
{
have : cos(5*pi/6) = cos((pi/2) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_776_test : cos(-2*pi) * cos(-pi)=cos(-2*pi)*cos(pi):=
begin
have : 1 / 2 * (2 * cos(pi) * cos((-2) * pi)) = cos(-2*pi)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) + cos(-3*pi) = 2 * cos(pi) * cos(-2*pi),
{
rw cos_add_cos,
have : cos(((-pi) + (-3*pi))/2) = cos(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (-3*pi))/2) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(-pi) + cos(-3*pi)) = cos(-pi)/2+cos(-3*pi)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-2*pi) * cos(-pi) = cos(-pi) / 2 + cos(-3*pi) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (-pi)) = cos(-3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (-pi)) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_777_test : sin(-pi/6)*cos(pi/2) + sin(pi/2)*cos(-pi/6)=- sin(154*pi/3):=
begin
have : sin(pi / 2) * cos(-pi / 6) + sin(-pi / 6) * cos(pi / 2) = sin(-pi/6)*cos(pi/2) + sin(pi/2)*cos(-pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(pi/2) * cos(-pi/6) + sin(-pi/6) * cos(pi/2),
{
have : sin(pi/3) = sin((pi/2) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(154*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_778_test : sin(5*pi/6)=-(-3*cos(-pi/18) + 4*cos(-pi/18)**3)*sin(-pi) + sin(-pi/6)*cos(-pi):=
begin
have : sin(-pi / 6) * cos(-pi) - sin(-pi) * (4 * cos(-pi / 18) ** 3 - 3 * cos(-pi / 18)) = -(-3*cos(-pi/18) + 4*cos(-pi/18)**3)*sin(-pi) + sin(-pi/6)*cos(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = 4 * cos(-pi/18) ** 3 - 3 * cos(-pi/18),
{
have : cos(-pi/6) = cos(3*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/6) = sin(-pi/6) * cos(-pi) - sin(-pi) * cos(-pi/6),
{
have : sin(5*pi/6) = sin((-pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_779_test (h0 : cos((-pi)/2)≠ 0) (h1 : sin(-pi)≠ 0) : (1 - cos(-pi))/sin(-pi)=- tan(101*pi/2):=
begin
have : tan(-pi/2) = ( 1 - cos(-pi) ) / sin(-pi),
{
have : tan(-pi/2) = tan((-pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - tan(101*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_780_test : sin(pi/3)=-cos(-149*pi/6):=
begin
have : -cos((-149) * pi / 6) = -cos(-149*pi/6),
{
field_simp at *,
},
have : cos(1133*pi/6) = cos(-149*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (1133*pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = - cos(1133*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_781_test : -sin(71*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = -sin(71*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_782_test : cos(463*pi/3)=sin(565*pi/6):=
begin
have : cos(-pi/3) = cos(463*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(565*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_783_test : sin(-5*pi/6)=-sin(pi/2)*sin(541*pi/6) + sin(-pi/3)*cos(pi/2):=
begin
have : sin(-pi / 3) * cos(pi / 2) - sin(pi / 2) * sin(541 * pi / 6) = -sin(pi/2)*sin(541*pi/6) + sin(-pi/3)*cos(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = sin(541*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/6) = sin(-pi/3) * cos(pi/2) - sin(pi/2) * cos(-pi/3),
{
have : sin(-5*pi/6) = sin((-pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_784_test : -cos(391*pi/2)=0:=
begin
have : cos(pi/2) = -cos(391*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_785_test (h0 : cos(-pi/2)≠ 0) (h1 : (2*cos(-pi/2)**2)≠ 0) (h2 : cos(-pi/2)≠ 0) (h3 : (2*cos(-pi/2))≠ 0) : sin(-pi)/(2*cos(-pi/2)**2)=tan(-pi/2):=
begin
have : sin(-pi) / (2 * cos(-pi / 2)) / cos(-pi / 2) = sin(-pi)/(2*cos(-pi/2)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-pi) / ( 2 * cos(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) / cos(-pi/2) = tan(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_786_test : sin(821*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = sin(821*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_787_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : sin(pi/3)/(2*sin(pi/6)) + cos(-2*pi)=2 * cos(-13*pi/12) * cos(-11*pi/12):=
begin
have : cos((-2) * pi) + sin(pi / 3) / (2 * sin(pi / 6)) = sin(pi/3)/(2*sin(pi/6)) + cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(pi/3) / ( 2 * sin(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(pi/6) = 2 * cos(-13*pi/12) * cos(-11*pi/12),
{
rw cos_add_cos,
have : cos(((-2*pi) + (pi/6))/2) = cos(-11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi/6))/2) = cos(-13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_789_test : -sin(839*pi/6)=1 / 2:=
begin
have : cos(pi/3) = -sin(839*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_790_test : -sin(2*pi/3) + sin(-pi/6)=2 * sin(-pi/4) * cos(pi/12):=
begin
have : sin(-pi / 6) + -sin(2 * pi / 3) = -sin(2*pi/3) + sin(-pi/6),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(2*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) + sin(-pi/3) = 2 * sin(-pi/4) * cos(pi/12),
{
rw sin_add_sin,
have : sin(((-pi/6) + (-pi/3))/2) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (-pi/3))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_792_test : sin(155*pi/6)=sin(595*pi/6):=
begin
have : sin(-pi/6) = sin(155*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(595*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_793_test : -cos(1549*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(1549*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_794_test : sin(-pi/2)*sin(pi/3) + cos(pi/2) - cos(-pi/2)*cos(pi/3)=- 2 * sin(pi/3) * sin(pi/6):=
begin
have : cos(pi / 2) - (-sin(-pi / 2) * sin(pi / 3) + cos(-pi / 2) * cos(pi / 3)) = sin(-pi/2)*sin(pi/3) + cos(pi/2) - cos(-pi/2)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/2) * sin(pi/3) + cos(-pi/2) * cos(pi/3),
{
have : cos(-pi/6) = cos((-pi/2) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) - cos(-pi/6) = - 2 * sin(pi/3) * sin(pi/6),
{
rw cos_sub_cos,
have : sin(((pi/2) + (-pi/6))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (-pi/6))/2) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_795_test : -cos(192*pi)=- sin(381*pi/2):=
begin
have : cos(-pi) = -cos(192*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(381*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_796_test : -cos(47*pi/2)=- sin(39*pi):=
begin
have : cos(-pi/2) = -cos(47*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - sin(39*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_797_test : sin(-2*pi/3)=-sin(-pi/3)*cos(85*pi) + sin(-pi)*cos(-pi/3):=
begin
have : sin(-pi) * cos(-pi / 3) - sin(-pi / 3) * cos(85 * pi) = -sin(-pi/3)*cos(85*pi) + sin(-pi)*cos(-pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = cos(85*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/3) = sin(-pi) * cos(-pi/3) - sin(-pi/3) * cos(-pi),
{
have : sin(-2*pi/3) = sin((-pi) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_798_test : cos(pi/3) ** 2=1 - sin(68*pi/3)**2:=
begin
have : sin(pi/3) = sin(68*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) ** 2 = 1 - sin(pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end




lemma Trigo_800_test : -sin(5*pi/12)**2 + cos(5*pi/12)**2=sin(-pi/6) * sin(-pi) + cos(-pi/6) * cos(-pi):=
begin
have : cos(5*pi/6) = -sin(5*pi/12) ** 2 + cos(5*pi/12) ** 2,
{
have : cos(5*pi/6) = cos(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = sin(-pi/6) * sin(-pi) + cos(-pi/6) * cos(-pi),
{
have : cos(5*pi/6) = cos((-pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_801_test (h0 : cos((pi/3)/2)≠ 0) (h1 : (cos(pi/3)+1)≠ 0) (h2 : (1+cos(pi/3))≠ 0) : sin(pi/3)/(cos(pi/3) + 1)=1 / tan(178*pi/3):=
begin
have : sin(pi / 3) / (1 + cos(pi / 3)) = sin(pi/3)/(cos(pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sin(pi/3) / ( 1 + cos(pi/3) ),
{
have : tan(pi/6) = tan((pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(178*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_802_test : cos(37*pi/3)=sin(pi/3) * sin(2*pi) + cos(pi/3) * cos(2*pi):=
begin
have : cos(-5*pi/3) = cos(37*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-5*pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/3) = sin(pi/3) * sin(2*pi) + cos(pi/3) * cos(2*pi),
{
have : cos(-5*pi/3) = cos((pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end




lemma Trigo_804_test : -sin(7*pi/2)=2 * cos(2*pi) ** 2 - 1:=
begin
have : cos(4*pi) = -sin(7*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = 2 * cos(2*pi) ** 2 - 1,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_805_test : -cos(157*pi/2)=- sin(184*pi):=
begin
have : sin(2*pi) = -cos(157*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(184*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_806_test : -sin(184*pi)=- sin(128*pi):=
begin
have : sin(-pi) = -sin(184*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(128*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_807_test : -tan(287*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = -tan(287*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_808_test (h0 : tan(187*pi/6)≠ 0) : -1/tan(187*pi/6)=1 / tan(77*pi/6):=
begin
have : (-1) / tan(187 * pi / 6) = -1/tan(187*pi/6),
{
field_simp at *,
},
have : tan(-pi/3) = -1 / tan(187*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = 1 / tan(77*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/3) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_809_test : sin(320*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = sin(320*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_810_test : cos(494*pi/3) + sin(pi/3)=2 * sin(pi/12) * cos(pi/4):=
begin
have : sin(pi / 3) + cos(494 * pi / 3) = cos(494*pi/3) + sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(494*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) + sin(-pi/6) = 2 * sin(pi/12) * cos(pi/4),
{
rw sin_add_sin,
have : sin(((pi/3) + (-pi/6))/2) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (-pi/6))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_811_test : -1 + 2*cos(-pi/4)**2=- sin(pi/2) * sin(-pi) + cos(pi/2) * cos(-pi):=
begin
have : 2 * cos(-pi / 4) ** 2 - 1 = -1 + 2*cos(-pi/4)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 2 * cos(-pi/4) ** 2 - 1,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - sin(pi/2) * sin(-pi) + cos(pi/2) * cos(-pi),
{
have : cos(-pi/2) = cos((pi/2) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_812_test : cos(-pi/2) + sin(pi/6)*sin(13*pi/6) + cos(pi/6)*cos(13*pi/6)=2 * cos(5*pi/4) * cos(3*pi/4):=
begin
have : sin(13 * pi / 6) * sin(pi / 6) + cos(13 * pi / 6) * cos(pi / 6) + cos(-pi / 2) = cos(-pi/2) + sin(pi/6)*sin(13*pi/6) + cos(pi/6)*cos(13*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(13*pi/6) * sin(pi/6) + cos(13*pi/6) * cos(pi/6),
{
have : cos(2*pi) = cos((13*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) + cos(-pi/2) = 2 * cos(5*pi/4) * cos(3*pi/4),
{
rw cos_add_cos,
have : cos(((2*pi) + (-pi/2))/2) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (-pi/2))/2) = cos(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_813_test : -cos(351*pi/2)=0:=
begin
have : cos(pi/2) = -cos(351*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end




lemma Trigo_815_test : cos(pi/3) - cos(83*pi)=2 * cos(-7*pi/6) * cos(-5*pi/6):=
begin
have : -cos(83 * pi) + cos(pi / 3) = cos(pi/3) - cos(83*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(83*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(pi/3) = 2 * cos(-7*pi/6) * cos(-5*pi/6),
{
rw cos_add_cos,
have : cos(((-2*pi) + (pi/3))/2) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi/3))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_816_test : -sin(371*pi/2)*cos(pi/2)=cos(-5*pi/2) / 2 + cos(-3*pi/2) / 2:=
begin
have : cos(-2*pi) = -sin(371*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) * cos(pi/2) = cos(-5*pi/2) / 2 + cos(-3*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (pi/2)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/2)) = cos(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_817_test : cos(233*pi/6)=- sin(469*pi/3):=
begin
have : sin(-pi/3) = cos(233*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(469*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_818_test : sin(251*pi/6)**2=1 / 2 - cos(pi/3) / 2:=
begin
have : (-sin(251 * pi / 6)) ** 2 = sin(251*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(251*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 / 2 - cos(pi/3) / 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_819_test (h0 : cos(329*pi/2)≠ 0) (h1 : (2*cos(329*pi/2))≠ 0) : cos(-2*pi)=sin(329*pi)/(2*cos(329*pi/2)):=
begin
have : sin(329*pi/2) = sin(329*pi) / ( 2 * cos(329*pi/2) ),
{
have : sin(329*pi) = sin(2*(329*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(329*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_821_test (h0 : tan(14*pi)≠ 0) : 1/tan(14*pi)=tan(109*pi/2):=
begin
have : tan(pi/2) = 1 / tan(14*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = tan(109*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_822_test : cos(121*pi)=- sin(-pi/2) ** 2 + cos(-pi/2) ** 2:=
begin
have : cos(-pi) = cos(121*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(-pi/2) ** 2 + cos(-pi/2) ** 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_823_test : sin(1393*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = sin(1393*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_824_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : sin(pi/3)/(2*sin(pi/6))=sin(248*pi/3):=
begin
have : cos(pi/6) = sin(pi/3) / ( 2 * sin(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(248*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_826_test : cos(0)*cos(pi) + sin(0)*sin(pi)=- sin(65*pi/2):=
begin
have : sin(0) * sin(pi) + cos(0) * cos(pi) = cos(0)*cos(pi) + sin(0)*sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(0) * sin(pi) + cos(0) * cos(pi),
{
have : cos(-pi) = cos((0) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(65*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_827_test : cos(295*pi/2)=- cos(367*pi/2):=
begin
have : sin(-pi) = cos(295*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - cos(367*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_828_test : sin(-pi/6)*cos(-11*pi/6) + sin(-11*pi/6)*cos(-pi/6)=- sin(175*pi):=
begin
have : sin((-11) * pi / 6) * cos(-pi / 6) + sin(-pi / 6) * cos((-11) * pi / 6) = sin(-pi/6)*cos(-11*pi/6) + sin(-11*pi/6)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-11*pi/6) * cos(-pi/6) + sin(-pi/6) * cos(-11*pi/6),
{
have : sin(-2*pi) = sin((-11*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(175*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_829_test (h0 : cos(pi/6)≠ 0) : sin(pi/6)/cos(pi/6)=1 / tan(7*pi/3):=
begin
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(7*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_830_test : sin(853*pi/6)=1 / 2:=
begin
have : cos(pi/3) = sin(853*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_831_test : sin(pi/3)=sin(410*pi/3):=
begin
have : cos(373*pi/6) = sin(410*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (373*pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = cos(373*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_832_test : (-4*sin(pi/18)**3 + 3*sin(pi/18))*cos(pi/2)=sin(-pi/3) / 2 + sin(2*pi/3) / 2:=
begin
have : ((-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18)) * cos(pi / 2) = (-4*sin(pi/18)**3 + 3*sin(pi/18))*cos(pi/2),
{
field_simp at *,
},
have : sin(pi/6) = -4 * sin(pi/18) ** 3 + 3 * sin(pi/18),
{
have : sin(pi/6) = sin(3*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(pi/2) = sin(-pi/3) / 2 + sin(2*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((pi/6) + (pi/2)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (pi/2)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_833_test : sin(17*pi)=0:=
begin
have : cos(pi/2) = sin(17*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_834_test : (-sin(-pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi/2))**2=1 / 2 - cos(-2*pi/3) / 2:=
begin
have : (sin((-5) * pi / 6) * cos(-pi / 2) - sin(-pi / 2) * cos((-5) * pi / 6)) ** 2 = (-sin(-pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi/2))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-5*pi/6) * cos(-pi/2) - sin(-pi/2) * cos(-5*pi/6),
{
have : sin(-pi/3) = sin((-5*pi/6) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) ** 2 = 1 / 2 - cos(-2*pi/3) / 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_835_test : sin(-pi/2)=-sin(-59*pi/2):=
begin
have : -sin((-59) * pi / 2) = -sin(-59*pi/2),
{
field_simp at *,
},
have : cos(140*pi) = sin(-59*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (140*pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = - cos(140*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_837_test (h0 : sin(-5*pi/6)≠ 0) (h1 : (4*sin(-5*pi/6))≠ 0) (h2 : (2*sin((-5)*pi/6))≠ 0) : sin(pi/6) * sin(-pi)=cos(7*pi/6)/2 - sin(-5*pi/3)/(4*sin(-5*pi/6)):=
begin
have : cos(7 * pi / 6) / 2 - sin((-5) * pi / 3) / (2 * sin((-5) * pi / 6)) / 2 = cos(7*pi/6)/2 - sin(-5*pi/3)/(4*sin(-5*pi/6)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/6) = sin(-5*pi/3) / ( 2 * sin(-5*pi/6) ),
{
have : sin(-5*pi/3) = sin(2*(-5*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) * sin(-pi) = cos(7*pi/6) / 2 - cos(-5*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((pi/6) + (-pi)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (-pi)) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_838_test : -cos(pi)=1:=
begin
have : sin(pi/2) = -cos(pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (0),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_839_test : (cos(-pi/2)*cos(-pi/3) + sin(-pi/2)*sin(-pi/3))*cos(-2*pi)=cos(-13*pi/6) / 2 + cos(-11*pi/6) / 2:=
begin
have : cos((-2) * pi) * (sin(-pi / 3) * sin(-pi / 2) + cos(-pi / 3) * cos(-pi / 2)) = (cos(-pi/2)*cos(-pi/3) + sin(-pi/2)*sin(-pi/3))*cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(-pi/3) * sin(-pi/2) + cos(-pi/3) * cos(-pi/2),
{
have : cos(pi/6) = cos((-pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) * cos(pi/6) = cos(-13*pi/6) / 2 + cos(-11*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (pi/6)) = cos(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/6)) = cos(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_840_test : -sin(47*pi/3)=2 * sin(pi/6) * cos(pi/6):=
begin
have : sin(pi/3) = -sin(47*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = 2 * sin(pi/6) * cos(pi/6),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end




lemma Trigo_842_test : cos(1045*pi/6) + cos(2*pi)=2 * cos(11*pi/12) * cos(13*pi/12):=
begin
have : cos(2 * pi) + cos(1045 * pi / 6) = cos(1045*pi/6) + cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(1045*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) + cos(pi/6) = 2 * cos(11*pi/12) * cos(13*pi/12),
{
rw cos_add_cos,
have : cos(((2*pi) + (pi/6))/2) = cos(13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (pi/6))/2) = cos(11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_843_test : -sin(323*pi/3)=2 * sin(pi/6) * cos(pi/6):=
begin
have : sin(pi/3) = -sin(323*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = 2 * sin(pi/6) * cos(pi/6),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_844_test : sin(-pi/6)=-sin(pi/2)*cos(pi/3) + (-sin(pi/4)**2 + cos(pi/4)**2)*sin(pi/3):=
begin
have : sin(pi / 3) * (-sin(pi / 4) ** 2 + cos(pi / 4) ** 2) - sin(pi / 2) * cos(pi / 3) = -sin(pi/2)*cos(pi/3) + (-sin(pi/4)**2 + cos(pi/4)**2)*sin(pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -sin(pi/4) ** 2 + cos(pi/4) ** 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = sin(pi/3) * cos(pi/2) - sin(pi/2) * cos(pi/3),
{
have : sin(-pi/6) = sin((pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end




lemma Trigo_846_test : sin(pi/2) - sin(pi/3)=-2*sin(pi/12)*sin(829*pi/12):=
begin
have : 2 * sin(pi / 12) * -sin(829 * pi / 12) = -2*sin(pi/12)*sin(829*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/12) = -sin(829*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/12) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) - sin(pi/3) = 2 * sin(pi/12) * cos(5*pi/12),
{
rw sin_sub_sin,
have : cos(((pi/2) + (pi/3))/2) = cos(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (pi/3))/2) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_847_test : -sin(196*pi)=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : cos(pi/2) = -sin(196*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 4 * cos(pi/6) ** 3 - 3 * cos(pi/6),
{
have : cos(pi/2) = cos(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_848_test : -1 + 2*cos(pi/4)**2=sin(101*pi):=
begin
have : 2 * cos(pi / 4) ** 2 - 1 = -1 + 2*cos(pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 2 * cos(pi/4) ** 2 - 1,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(101*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_849_test (h0 : tan(280*pi/3)≠ 0) : 1/tan(280*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(280*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_850_test : 3*sin(-pi/6) - 4*sin(-pi/6)**3=- sin(197*pi/2):=
begin
have : (-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6) = 3*sin(-pi/6) - 4*sin(-pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6),
{
have : sin(-pi/2) = sin(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(197*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_851_test : cos(533*pi/6)=sin(-pi/3) * cos(pi/3) - sin(pi/3) * cos(-pi/3):=
begin
have : sin(-2*pi/3) = cos(533*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/3) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = sin(-pi/3) * cos(pi/3) - sin(pi/3) * cos(-pi/3),
{
have : sin(-2*pi/3) = sin((-pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_852_test : cos(-3*pi/2)=-sin(2*pi)*cos(179*pi) + cos(pi/2)*cos(2*pi):=
begin
have : -cos(179 * pi) * sin(2 * pi) + cos(pi / 2) * cos(2 * pi) = -sin(2*pi)*cos(179*pi) + cos(pi/2)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = -cos(179*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-3*pi/2) = sin(pi/2) * sin(2*pi) + cos(pi/2) * cos(2*pi),
{
have : cos(-3*pi/2) = cos((pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_853_test : sin(-pi/6)=sin(pi/2)*sin(847*pi/6) - cos(pi/2)*cos(847*pi/6):=
begin
have : -(-sin(847 * pi / 6) * sin(pi / 2) + cos(847 * pi / 6) * cos(pi / 2)) = sin(pi/2)*sin(847*pi/6) - cos(pi/2)*cos(847*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(425*pi/3) = -sin(847*pi/6) * sin(pi/2) + cos(847*pi/6) * cos(pi/2),
{
have : cos(425*pi/3) = cos((847*pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = - cos(425*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_854_test : cos(pi)=sin(55*pi/2):=
begin
have : sin(-pi/2) = sin(55*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = sin(-pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_855_test : 2*sin(pi/2)*cos(pi/2)=- sin(29*pi):=
begin
have : sin(pi) = 2 * sin(pi/2) * cos(pi/2),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(29*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_857_test : cos(4*pi)=1 - 2*sin(17*pi)**2:=
begin
have : sin(2*pi) = sin(17*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi) = 1 - 2 * sin(2*pi) ** 2,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_858_test : -cos(191*pi)=sin(pi/3) * cos(pi/6) + sin(pi/6) * cos(pi/3):=
begin
have : sin(pi/2) = -cos(191*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(pi/3) * cos(pi/6) + sin(pi/6) * cos(pi/3),
{
have : sin(pi/2) = sin((pi/3) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_859_test : 3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3=sin(47*pi):=
begin
have : (-4) * sin((-2) * pi / 3) ** 3 + 3 * sin((-2) * pi / 3) = 3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -4 * sin(-2*pi/3) ** 3 + 3 * sin(-2*pi/3),
{
have : sin(-2*pi) = sin(3*(-2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(47*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_860_test : -3*cos(-2*pi/9) + 4*cos(-2*pi/9)**3=- sin(pi/3) * sin(-pi) + cos(pi/3) * cos(-pi):=
begin
have : 4 * cos((-2) * pi / 9) ** 3 - 3 * cos((-2) * pi / 9) = -3*cos(-2*pi/9) + 4*cos(-2*pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = 4 * cos(-2*pi/9) ** 3 - 3 * cos(-2*pi/9),
{
have : cos(-2*pi/3) = cos(3*(-2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = - sin(pi/3) * sin(-pi) + cos(pi/3) * cos(-pi),
{
have : cos(-2*pi/3) = cos((pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_861_test : -sin(34*pi)=- cos(281*pi/2):=
begin
have : cos(-pi/2) = -sin(34*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(281*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_862_test : -sin(215*pi/2)=2 * cos(pi) ** 2 - 1:=
begin
have : cos(2*pi) = -sin(215*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 2 * cos(pi) ** 2 - 1,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
rw this,
end


lemma Trigo_863_test : cos(-pi/6)*cos(pi/2) - sin(-pi/6)*sin(pi/2)=1 - 2 * sin(pi/6) ** 2:=
begin
have : -sin(-pi / 6) * sin(pi / 2) + cos(-pi / 6) * cos(pi / 2) = cos(-pi/6)*cos(pi/2) - sin(-pi/6)*sin(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(-pi/6) * sin(pi/2) + cos(-pi/6) * cos(pi/2),
{
have : cos(pi/3) = cos((-pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_864_test (h0 : cos(275*pi/6)≠ 0) : sin(-pi/6)/cos(275*pi/6)=tan(-pi/6):=
begin
have : cos(-pi/6) = cos(275*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) / cos(-pi/6) = tan(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_866_test : -cos(2*pi)*cos(201*pi)=cos(4*pi) / 2 + cos(0) / 2:=
begin
have : cos(2 * pi) * -cos(201 * pi) = -cos(2*pi)*cos(201*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(201*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) * cos(-2*pi) = cos(4*pi) / 2 + cos(0) / 2,
{
rw cos_mul_cos,
have : cos((2*pi) + (-2*pi)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (-2*pi)) = cos(4*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_867_test : sin(pi)=4*cos(55*pi/2)**3 - 3*cos(55*pi/2):=
begin
have : cos(165*pi/2) = 4 * cos(55*pi/2) ** 3 - 3 * cos(55*pi/2),
{
have : cos(165*pi/2) = cos(3*(55*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = cos(165*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_868_test : -cos(142*pi/3)=2 * cos(pi/6) ** 2 - 1:=
begin
have : cos(pi/3) = -cos(142*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 2 * cos(pi/6) ** 2 - 1,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_869_test : sin(91*pi/6)=sin(1159*pi/6):=
begin
have : sin(-pi/6) = sin(91*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(1159*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_871_test : sin(5*pi/3)*cos(-pi/3) - sin(-pi/3)*cos(5*pi/3)=cos(361*pi/2):=
begin
have : sin(2*pi) = sin(5*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(5*pi/3),
{
have : sin(2*pi) = sin((5*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(361*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_872_test : (sin(5*pi/2)*cos(-pi/2) + sin(-pi/2)*cos(5*pi/2))*sin(pi)=cos(-pi) / 2 - cos(3*pi) / 2:=
begin
have : sin(pi) * (sin(5 * pi / 2) * cos(-pi / 2) + sin(-pi / 2) * cos(5 * pi / 2)) = (sin(5*pi/2)*cos(-pi/2) + sin(-pi/2)*cos(5*pi/2))*sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(5*pi/2) * cos(-pi/2) + sin(-pi/2) * cos(5*pi/2),
{
have : sin(2*pi) = sin((5*pi/2) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * sin(2*pi) = cos(-pi) / 2 - cos(3*pi) / 2,
{
rw sin_mul_sin,
have : cos((pi) + (2*pi)) = cos(3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (2*pi)) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_873_test : sin(194*pi)**2=1 - sin(-pi/2) ** 2:=
begin
have : cos(-pi/2) = sin(194*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) ** 2 = 1 - sin(-pi/2) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_874_test : -sin(-pi)**2 + cos(-pi)**2=- sin(207*pi/2):=
begin
have : cos(-2*pi) = -sin(-pi) ** 2 + cos(-pi) ** 2,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - sin(207*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_875_test : cos(130*pi)=- 4 * sin(pi/6) ** 3 + 3 * sin(pi/6):=
begin
have : sin(pi/2) = cos(130*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - 4 * sin(pi/6) ** 3 + 3 * sin(pi/6),
{
have : sin(pi/2) = sin(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_876_test : sin(-pi)=cos(133*pi/2):=
begin
have : - -cos(133 * pi / 2) = cos(133*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(165*pi/2) = -cos(133*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (165*pi/2) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(165*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_878_test (h0 : sin(3*pi)≠ 0) (h1 : (2*sin(3*pi))≠ 0) (h2 : (4*sin(3*pi))≠ 0) : sin(2*pi) * sin(-pi)=sin(6*pi)/(4*sin(3*pi)) - cos(pi)/2:=
begin
have : sin(6 * pi) / (2 * sin(3 * pi)) / 2 - cos(pi) / 2 = sin(6*pi)/(4*sin(3*pi)) - cos(pi)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi) = sin(6*pi) / ( 2 * sin(3*pi) ),
{
have : sin(6*pi) = sin(2*(3*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * sin(-pi) = cos(3*pi) / 2 - cos(pi) / 2,
{
rw sin_mul_sin,
have : cos((2*pi) + (-pi)) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (-pi)) = cos(3*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_879_test : sin(-pi/3) + sin(-pi/6)=sin(-pi/3) - sin(pi/6):=
begin
have : 2 * (-sin(pi / 6) / 2 + sin(-pi / 3) / 2) = sin(-pi/3) - sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) * cos(-pi/12) = -sin(pi/6) / 2 + sin(-pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/12) + (-pi/4)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/12) - (-pi/4)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-pi/4) * cos(-pi/12)) = 2*sin(-pi/4)*cos(-pi/12),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi/3) + sin(-pi/6) = 2 * sin(-pi/4) * cos(-pi/12),
{
rw sin_add_sin,
have : sin(((-pi/3) + (-pi/6))/2) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (-pi/6))/2) = cos(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_881_test : cos(3*pi/2)=-(-sin(-2*pi)*cos(-3*pi/2) + sin(-3*pi/2)*cos(-2*pi))*sin(pi) + cos(pi/2)*cos(pi):=
begin
have : -(sin((-3) * pi / 2) * cos((-2) * pi) - sin((-2) * pi) * cos((-3) * pi / 2)) * sin(pi) + cos(pi / 2) * cos(pi) = -(-sin(-2*pi)*cos(-3*pi/2) + sin(-3*pi/2)*cos(-2*pi))*sin(pi) + cos(pi/2)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(-3*pi/2) * cos(-2*pi) - sin(-2*pi) * cos(-3*pi/2),
{
have : sin(pi/2) = sin((-3*pi/2) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/2) = - sin(pi/2) * sin(pi) + cos(pi/2) * cos(pi),
{
have : cos(3*pi/2) = cos((pi/2) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_882_test : sin(-pi/2)=-cos(108*pi):=
begin
have : cos(58*pi) = cos(108*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (58*pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = - cos(58*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_883_test : sin(-pi/3) * sin(-2*pi)=-1/2 + sin(-7*pi/6)**2 + cos(5*pi/3)/2:=
begin
have : cos(5 * pi / 3) / 2 - (1 - 2 * sin((-7) * pi / 6) ** 2) / 2 = -1/2 + sin(-7*pi/6)**2 + cos(5*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-7*pi/3) = 1 - 2 * sin(-7*pi/6) ** 2,
{
have : cos(-7*pi/3) = cos(2*(-7*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) * sin(-2*pi) = cos(5*pi/3) / 2 - cos(-7*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((-pi/3) + (-2*pi)) = cos(-7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/3) - (-2*pi)) = cos(5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_884_test : cos(pi/6) - cos(171*pi)=2 * cos(13*pi/12) * cos(-11*pi/12):=
begin
have : cos(pi / 6) + -cos(171 * pi) = cos(pi/6) - cos(171*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(171*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) + cos(-2*pi) = 2 * cos(13*pi/12) * cos(-11*pi/12),
{
rw cos_add_cos,
have : cos(((pi/6) + (-2*pi))/2) = cos(-11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/6) - (-2*pi))/2) = cos(13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_885_test : -sin(pi/3)*cos(7*pi/3) + sin(7*pi/3)*cos(pi/3)=- sin(139*pi):=
begin
have : sin(7 * pi / 3) * cos(pi / 3) - sin(pi / 3) * cos(7 * pi / 3) = -sin(pi/3)*cos(7*pi/3) + sin(7*pi/3)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(7*pi/3) * cos(pi/3) - sin(pi/3) * cos(7*pi/3),
{
have : sin(2*pi) = sin((7*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(139*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_886_test : sin(-2*pi)=-cos(-119*pi/2):=
begin
have : -cos((-119) * pi / 2) = -cos(-119*pi/2),
{
field_simp at *,
},
have : cos(291*pi/2) = cos(-119*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (291*pi/2) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = - cos(291*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_888_test : -3*cos(-pi/6) + 4*cos(-pi/6)**3=- sin(178*pi):=
begin
have : 4 * cos(-pi / 6) ** 3 - 3 * cos(-pi / 6) = -3*cos(-pi/6) + 4*cos(-pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6),
{
have : cos(-pi/2) = cos(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - sin(178*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_890_test : sin(-pi)*sin(pi/2) + cos(-pi)*cos(pi/2)=sin(2*pi) * sin(pi/2) + cos(2*pi) * cos(pi/2):=
begin
have : sin(pi / 2) * sin(-pi) + cos(pi / 2) * cos(-pi) = sin(-pi)*sin(pi/2) + cos(-pi)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/2) = sin(pi/2) * sin(-pi) + cos(pi/2) * cos(-pi),
{
have : cos(3*pi/2) = cos((pi/2) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/2) = sin(2*pi) * sin(pi/2) + cos(2*pi) * cos(pi/2),
{
have : cos(3*pi/2) = cos((2*pi) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end




lemma Trigo_892_test : sin(-pi/3) / cos(-pi/3)=-tan(37*pi/3):=
begin
have : tan(-pi/3) = -tan(37*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_893_test : -tan(125*pi/4)=- 1:=
begin
have : tan(3*pi/4) = -tan(125*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_894_test : -sin(1111*pi/6)=1 / 2:=
begin
have : sin(pi/6) = -sin(1111*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_895_test : cos(347*pi/6)=sin(194*pi/3):=
begin
have : cos(-pi/6) = cos(347*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(194*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_896_test : sin(87*pi/2)=cos(153*pi):=
begin
have : cos(-pi) = sin(87*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(153*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_899_test : -tan(2*pi)=- 1 / tan(73*pi/2):=
begin
have : tan(pi) = -tan(2*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(73*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_900_test : (cos(-2*pi)*cos(-3*pi/2) + sin(-2*pi)*sin(-3*pi/2))*sin(-pi/2)=sin(-pi) / 2 + sin(0) / 2:=
begin
have : sin(-pi / 2) * (sin((-3) * pi / 2) * sin((-2) * pi) + cos((-3) * pi / 2) * cos((-2) * pi)) = (cos(-2*pi)*cos(-3*pi/2) + sin(-2*pi)*sin(-3*pi/2))*sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(-3*pi/2) * sin(-2*pi) + cos(-3*pi/2) * cos(-2*pi),
{
have : cos(pi/2) = cos((-3*pi/2) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(pi/2) = sin(-pi) / 2 + sin(0) / 2,
{
rw sin_mul_cos,
have : sin((-pi/2) + (pi/2)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (pi/2)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_901_test (h0 : tan(133*pi/2)≠ 0) : 1/tan(133*pi/2)=1 / tan(193*pi/2):=
begin
have : tan(-pi) = 1 / tan(133*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = 1 / tan(193*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_903_test : cos(-2*pi)=2*sin(237*pi/4)*cos(237*pi/4):=
begin
have : sin(237*pi/2) = 2 * sin(237*pi/4) * cos(237*pi/4),
{
have : sin(237*pi/2) = sin(2*(237*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(237*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_904_test (h0 : tan(313*pi/4)≠ 0) : 1/tan(313*pi/4)=1:=
begin
have : tan(pi/4) = 1 / tan(313*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_905_test : -1 + 2*cos(-pi/2)**2=cos(25*pi):=
begin
have : 2 * cos(-pi / 2) ** 2 - 1 = -1 + 2*cos(-pi/2)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = 2 * cos(-pi/2) ** 2 - 1,
{
have : cos(-pi) = cos(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(25*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_906_test (h0 : tan(94*pi/3)≠ 0) : 1/tan(94*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(94*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_907_test : cos(357*pi/2)=sin(36*pi):=
begin
have : sin(2*pi) = cos(357*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(36*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_908_test (h0 : tan(27*pi)≠ 0) : -1/tan(27*pi)=- tan(91*pi/2):=
begin
have : (-1) / tan(27 * pi) = -1/tan(27*pi),
{
field_simp at *,
},
have : tan(-pi/2) = -1 / tan(27*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - tan(91*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_910_test : tan(153*pi/2)=- tan(159*pi/2):=
begin
have : tan(-pi/2) = tan(153*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - tan(159*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_911_test : sin(61*pi)=- cos(263*pi/2):=
begin
have : cos(-pi/2) = sin(61*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(263*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_912_test : sin(541*pi/6)=1 / 2:=
begin
have : sin(pi/6) = sin(541*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_913_test : sin(pi/6)=-sin(719*pi/6):=
begin
have : cos(116*pi/3) = sin(719*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (116*pi/3) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(116*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_914_test : tan(167*pi/3)=tan(266*pi/3):=
begin
have : tan(-pi/3) = tan(167*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (-pi/3) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = tan(266*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (-pi/3) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_915_test : sin(1063*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = sin(1063*pi/12),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/12) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_916_test : cos(pi)=-sin(105*pi/2)**2 + cos(pi/2)**2:=
begin
have : sin(pi/2) = sin(105*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = - sin(pi/2) ** 2 + cos(pi/2) ** 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_917_test : -sin(pi/3) + sin(262*pi/3)=2 * sin(-pi/3) * cos(0):=
begin
have : sin(262 * pi / 3) - sin(pi / 3) = -sin(pi/3) + sin(262*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(262*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) - sin(pi/3) = 2 * sin(-pi/3) * cos(0),
{
rw sin_sub_sin,
have : cos(((-pi/3) + (pi/3))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (pi/3))/2) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_918_test : -cos(571*pi/3)=- sin(1169*pi/6):=
begin
have : sin(-pi/6) = -cos(571*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(1169*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_919_test : cos(pi/3)**2 + sin(374*pi/3)**2=1:=
begin
have : sin(374 * pi / 3) ** 2 + cos(pi / 3) ** 2 = cos(pi/3)**2 + sin(374*pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(374*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 + cos(pi/3) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_920_test : cos(-pi/2)=sin(-pi/6)*sin(61*pi/3) + cos(-pi/3)*cos(-pi/6):=
begin
have : - -sin(61 * pi / 3) * sin(-pi / 6) + cos(-pi / 3) * cos(-pi / 6) = sin(-pi/6)*sin(61*pi/3) + cos(-pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = -sin(61*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(-pi/3) * sin(-pi/6) + cos(-pi/3) * cos(-pi/6),
{
have : cos(-pi/2) = cos((-pi/3) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_921_test : cos(49*pi/6)=cos(299*pi/6):=
begin
have : cos(pi/6) = cos(49*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(299*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_922_test : cos(685*pi/6)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = cos(685*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_923_test : sin(521*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = sin(521*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_924_test : sin(-pi)*sin(-2*pi/3) + cos(-pi)*cos(-2*pi/3)=1 - 2 * sin(pi/6) ** 2:=
begin
have : sin((-2) * pi / 3) * sin(-pi) + cos((-2) * pi / 3) * cos(-pi) = sin(-pi)*sin(-2*pi/3) + cos(-pi)*cos(-2*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(-2*pi/3) * sin(-pi) + cos(-2*pi/3) * cos(-pi),
{
have : cos(pi/3) = cos((-2*pi/3) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end




lemma Trigo_926_test : sin(pi/3)=sin(320*pi/3):=
begin
have : - -sin(320 * pi / 3) = sin(320*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(571*pi/6) = -sin(320*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (571*pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = - cos(571*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end






lemma Trigo_929_test : -cos(169*pi/6)=cos(1085*pi/6):=
begin
have : sin(-pi/3) = -cos(169*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(1085*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_930_test : -cos(227*pi/2) + cos(-pi/3)=2 * cos(-5*pi/12) * cos(pi/12):=
begin
have : cos(-pi / 3) + -cos(227 * pi / 2) = -cos(227*pi/2) + cos(-pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(227*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(pi/2) = 2 * cos(-5*pi/12) * cos(pi/12),
{
rw cos_add_cos,
have : cos(((-pi/3) + (pi/2))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (pi/2))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_931_test : cos(pi)=3*sin(227*pi/6) - 4*sin(227*pi/6)**3:=
begin
have : (-4) * sin(227 * pi / 6) ** 3 + 3 * sin(227 * pi / 6) = 3*sin(227*pi/6) - 4*sin(227*pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(227*pi/2) = -4 * sin(227*pi/6) ** 3 + 3 * sin(227*pi/6),
{
have : sin(227*pi/2) = sin(3*(227*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = sin(227*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_932_test : sin(pi/2)=-cos(41*pi):=
begin
have : cos(116*pi) = -cos(41*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (116*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = cos(116*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_933_test : cos(86*pi)=- cos(99*pi):=
begin
have : sin(pi/2) = cos(86*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - cos(99*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_935_test (h0 : cos(91*pi)≠ 0) (h1 : (2*cos(91*pi))≠ 0) : cos(pi/2)=-sin(182*pi)/(2*cos(91*pi)):=
begin
have : -(sin(182 * pi) / (2 * cos(91 * pi))) = -sin(182*pi)/(2*cos(91*pi)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(91*pi) = sin(182*pi) / ( 2 * cos(91*pi) ),
{
have : sin(182*pi) = sin(2*(91*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(91*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_936_test (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : sin(2*pi/3)*cos(-2*pi)/(2*cos(pi/3))=sin(7*pi/3) / 2 + sin(-5*pi/3) / 2:=
begin
have : sin(2 * pi / 3) / (2 * cos(pi / 3)) * cos((-2) * pi) = sin(2*pi/3)*cos(-2*pi)/(2*cos(pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(2*pi/3) / ( 2 * cos(pi/3) ),
{
have : sin(2*pi/3) = sin(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(-2*pi) = sin(7*pi/3) / 2 + sin(-5*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (-2*pi)) = sin(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-2*pi)) = sin(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_937_test : sin(25*pi/2)=- 4 * sin(-pi/2) ** 3 + 3 * sin(-pi/2):=
begin
have : sin(-3*pi/2) = sin(25*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-3*pi/2) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2) = - 4 * sin(-pi/2) ** 3 + 3 * sin(-pi/2),
{
have : sin(-3*pi/2) = sin(3*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_938_test : -sin(pi)*sin(22*pi)=sin(3*pi/2) / 2 + sin(pi/2) / 2:=
begin
have : sin(pi) * -sin(22 * pi) = -sin(pi)*sin(22*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(22*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(-pi/2) = sin(3*pi/2) / 2 + sin(pi/2) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (-pi/2)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (-pi/2)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_941_test : tan(135*pi/2)=1 / tan(18*pi):=
begin
have : tan(-pi/2) = tan(135*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = 1 / tan(18*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/2) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_942_test : -sin(241*pi/2)=- 1:=
begin
have : cos(pi) = -sin(241*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_943_test : sin(pi)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi)=- sin(10*pi/3):=
begin
have : sin((-2) * pi / 3) * cos(pi) + sin(pi) * cos((-2) * pi / 3) = sin(pi)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(-2*pi/3) * cos(pi) + sin(pi) * cos(-2*pi/3),
{
have : sin(pi/3) = sin((-2*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(10*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_944_test : -sin(191*pi)=- sin(80*pi):=
begin
have : sin(pi) = -sin(191*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(80*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_946_test : cos(-9*pi/2)*cos(-pi/2) + sin(-9*pi/2)*sin(-pi/2)=1 - 2 * sin(-2*pi) ** 2:=
begin
have : sin((-9) * pi / 2) * sin(-pi / 2) + cos((-9) * pi / 2) * cos(-pi / 2) = cos(-9*pi/2)*cos(-pi/2) + sin(-9*pi/2)*sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-4*pi) = sin(-9*pi/2) * sin(-pi/2) + cos(-9*pi/2) * cos(-pi/2),
{
have : cos(-4*pi) = cos((-9*pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-4*pi) = 1 - 2 * sin(-2*pi) ** 2,
{
have : cos(-4*pi) = cos(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_947_test (h0 : cos((-pi/3)/2)≠ 0) (h1 : (cos(-pi/3)+1)≠ 0) (h2 : (1+cos(-pi/3))≠ 0) : sin(-pi/3)/(cos(-pi/3) + 1)=- tan(289*pi/6):=
begin
have : sin(-pi / 3) / (1 + cos(-pi / 3)) = sin(-pi/3)/(cos(-pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = sin(-pi/3) / ( 1 + cos(-pi/3) ),
{
have : tan(-pi/6) = tan((-pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - tan(289*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/6) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_948_test : -sin(925*pi/6)=2 * cos(-pi/3) ** 2 - 1:=
begin
have : cos(-2*pi/3) = -sin(925*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/3) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = 2 * cos(-pi/3) ** 2 - 1,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_949_test : sin(75*pi)*cos(-2*pi)=sin(pi) / 2 + sin(-3*pi) / 2:=
begin
have : sin(75 * pi) * cos((-2) * pi) = sin(75*pi)*cos(-2*pi),
{
field_simp at *,
},
have : sin(-pi) = sin(75*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * cos(-2*pi) = sin(pi) / 2 + sin(-3*pi) / 2,
{
rw sin_mul_cos,
have : sin((-pi) + (-2*pi)) = sin(-3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (-2*pi)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_950_test : sin(322*pi/3)*cos(pi)=- sin(4*pi/3) / 2 + sin(2*pi/3) / 2:=
begin
have : sin(-pi/3) = sin(322*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi) = - sin(4*pi/3) / 2 + sin(2*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi) + (-pi/3)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (-pi/3)) = sin(4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_951_test : sin(pi/3) ** 2=-cos(pi/6)*cos(pi/2)/2 + sin(pi/6)*sin(pi/2)/2 + 1/2:=
begin
have : 1 / 2 - (-sin(pi / 2) * sin(pi / 6) + cos(pi / 2) * cos(pi / 6)) / 2 = -cos(pi/6)*cos(pi/2)/2 + sin(pi/6)*sin(pi/2)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/3) = -sin(pi/2) * sin(pi/6) + cos(pi/2) * cos(pi/6),
{
have : cos(2*pi/3) = cos((pi/2) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) ** 2 = 1 / 2 - cos(2*pi/3) / 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_952_test : -sin(599*pi/3)=cos(397*pi/6):=
begin
have : cos(pi/6) = -sin(599*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(397*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_953_test (h0 : tan(325*pi/4)≠ 0) : 1/tan(325*pi/4)=1:=
begin
have : tan(pi/4) = 1 / tan(325*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_954_test : -sin(180*pi)=- cos(357*pi/2):=
begin
have : cos(-pi/2) = -sin(180*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(357*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_955_test : cos(135*pi/2) + cos(pi/3)=2 * cos(-pi/12) * cos(5*pi/12):=
begin
have : cos(pi / 3) + cos(135 * pi / 2) = cos(135*pi/2) + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(135*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) + cos(pi/2) = 2 * cos(-pi/12) * cos(5*pi/12),
{
rw cos_add_cos,
have : cos(((pi/3) + (pi/2))/2) = cos(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (pi/2))/2) = cos(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_956_test : -cos(587*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(587*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_957_test : -tan(343*pi/4)=1:=
begin
have : tan(pi/4) = -tan(343*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_958_test : 2*sin(-pi/4)*cos(-pi/4)=sin(11*pi/2):=
begin
have : sin(-pi/2) = 2 * sin(-pi/4) * cos(-pi/4),
{
have : sin(-pi/2) = sin(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(11*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_960_test : sin(1115*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = sin(1115*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_961_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : cos(-pi) + sin(pi/3)/(2*sin(pi/6))=2 * cos(-7*pi/12) * cos(-5*pi/12):=
begin
have : cos(pi/6) = sin(pi/3) / ( 2 * sin(pi/6) ),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) + cos(pi/6) = 2 * cos(-7*pi/12) * cos(-5*pi/12),
{
rw cos_add_cos,
have : cos(((-pi) + (pi/6))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (pi/6))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_962_test : -sin(337*pi/3)=sin(599*pi/3):=
begin
have : sin(-pi/3) = -sin(337*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(599*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_963_test : sin(-pi/2)*sin(421*pi/6)=- sin(5*pi/6) / 2 + sin(-pi/6) / 2:=
begin
have : cos(pi/3) = sin(421*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(pi/3) = - sin(5*pi/6) / 2 + sin(-pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/2)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/2)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_964_test (h0 : cos(-2*pi)≠ 0) : -sin(7*pi)=sin(-4*pi) / ( 2 * cos(-2*pi) ):=
begin
have : sin(-2*pi) = -sin(7*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-4*pi) / ( 2 * cos(-2*pi) ),
{
have : sin(-4*pi) = sin(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
rw this,
end


lemma Trigo_965_test : cos(124*pi/3)=2 * cos(pi/3) ** 2 - 1:=
begin
have : cos(2*pi/3) = cos(124*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = 2 * cos(pi/3) ** 2 - 1,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_966_test : sin(91*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = sin(91*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_967_test : -3*cos(pi/18) + 4*cos(pi/18)**3=cos(745*pi/6):=
begin
have : 4 * cos(pi / 18) ** 3 - 3 * cos(pi / 18) = -3*cos(pi/18) + 4*cos(pi/18)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = 4 * cos(pi/18) ** 3 - 3 * cos(pi/18),
{
have : cos(pi/6) = cos(3*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(745*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_968_test : cos(-pi)=3*sin(179*pi/6) - 4*sin(179*pi/6)**3:=
begin
have : (-4) * sin(179 * pi / 6) ** 3 + 3 * sin(179 * pi / 6) = 3*sin(179*pi/6) - 4*sin(179*pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(179*pi/2) = -4 * sin(179*pi/6) ** 3 + 3 * sin(179*pi/6),
{
have : sin(179*pi/2) = sin(3*(179*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(179*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_969_test : -sin(93*pi)=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : cos(pi/2) = -sin(93*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 4 * cos(pi/6) ** 3 - 3 * cos(pi/6),
{
have : cos(pi/2) = cos(3*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_970_test (h0 : tan(229*pi/3)≠ 0) : 1/tan(229*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(229*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_971_test : sin(pi) * sin(pi/2)=sin(26*pi)/2 + cos(pi/2)/2:=
begin
have : cos(pi / 2) / 2 - -sin(26 * pi) / 2 = sin(26*pi)/2 + cos(pi/2)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/2) = -sin(26*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * sin(pi/2) = cos(pi/2) / 2 - cos(3*pi/2) / 2,
{
rw sin_mul_sin,
have : cos((pi) + (pi/2)) = cos(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (pi/2)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_972_test : sin(-pi/3)*cos(11*pi/6) + sin(11*pi/6)*cos(-pi/3)=- 4 * sin(pi/2) ** 3 + 3 * sin(pi/2):=
begin
have : sin(11 * pi / 6) * cos(-pi / 3) + sin(-pi / 3) * cos(11 * pi / 6) = sin(-pi/3)*cos(11*pi/6) + sin(11*pi/6)*cos(-pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/2) = sin(11*pi/6) * cos(-pi/3) + sin(-pi/3) * cos(11*pi/6),
{
have : sin(3*pi/2) = sin((11*pi/6) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/2) = - 4 * sin(pi/2) ** 3 + 3 * sin(pi/2),
{
have : sin(3*pi/2) = sin(3*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_973_test : -sin(50*pi)=- 4 * sin(-pi/3) ** 3 + 3 * sin(-pi/3):=
begin
have : sin(-pi) = -sin(50*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - 4 * sin(-pi/3) ** 3 + 3 * sin(-pi/3),
{
have : sin(-pi) = sin(3*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_974_test : cos(48*pi)**2=1 - cos(pi/2) ** 2:=
begin
have : sin(pi/2) = cos(48*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) ** 2 = 1 - cos(pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_975_test : -tan(52*pi/3)=- tan(184*pi/3):=
begin
have : tan(-pi/3) = -tan(52*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - tan(184*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_976_test : tan(73*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = tan(73*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_977_test : sin(1139*pi/6)**2=1 / 2 - cos(-pi/3) / 2:=
begin
have : sin(-pi/6) = sin(1139*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) ** 2 = 1 / 2 - cos(-pi/3) / 2,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end






lemma Trigo_980_test : -cos(122*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(122*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end






lemma Trigo_983_test : -cos(99*pi/2) + cos(-pi/3)=2 * cos(-pi/12) * cos(-5*pi/12):=
begin
have : cos(-pi/2) = -cos(99*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) + cos(-pi/3) = 2 * cos(-pi/12) * cos(-5*pi/12),
{
rw cos_add_cos,
have : cos(((-pi/2) + (-pi/3))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (-pi/3))/2) = cos(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_984_test : -cos(32*pi/3)=1 - 2 * sin(pi/6) ** 2:=
begin
have : cos(pi/3) = -cos(32*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 - 2 * sin(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_985_test (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : (1 - cos(2*pi))/sin(2*pi)=- 1 / tan(161*pi/2):=
begin
have : tan(pi) = ( 1 - cos(2*pi) ) / sin(2*pi),
{
have : tan(pi) = tan((2*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(161*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_986_test : tan(33*pi/2)=tan(23*pi/2):=
begin
have : tan(-pi/2) = tan(33*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = tan(23*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_987_test : sin(4*pi/3)*cos(pi/3) - sin(pi/3)*cos(4*pi/3)=2 * sin(pi/2) * cos(pi/2):=
begin
have : sin(pi) = sin(4*pi/3) * cos(pi/3) - sin(pi/3) * cos(4*pi/3),
{
have : sin(pi) = sin((4*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 2 * sin(pi/2) * cos(pi/2),
{
have : sin(pi) = sin(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_988_test : sin(-pi) * sin(-pi/3)=-sin(-pi)*sin(pi/3):=
begin
have : 1 / 2 * ((-2) * sin(pi / 3) * sin(-pi)) = -sin(-pi)*sin(pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) - cos(-4*pi/3) = -2 * sin(pi/3) * sin(-pi),
{
rw cos_sub_cos,
have : sin(((-2*pi/3) + (-4*pi/3))/2) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-2*pi/3) - (-4*pi/3))/2) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(-2*pi/3) - cos(-4*pi/3)) = cos(-2*pi/3)/2-cos(-4*pi/3)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi) * sin(-pi/3) = cos(-2*pi/3) / 2 - cos(-4*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((-pi) + (-pi/3)) = cos(-4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-pi/3)) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_989_test (h0 : sin(-pi/2)≠ 0) (h1 : (2*sin(-pi/2))≠ 0) (h2 : sin(-pi/2)≠ 0) : sin(-pi/2) + sin(pi/2)=sin(0)*sin(-pi)/sin(-pi/2):=
begin
have : 2 * sin(0) * (sin(-pi) / (2 * sin(-pi / 2))) = sin(0)*sin(-pi)/sin(-pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(-pi) / ( 2 * sin(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) + sin(pi/2) = 2 * sin(0) * cos(-pi/2),
{
rw sin_add_sin,
have : sin(((-pi/2) + (pi/2))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (pi/2))/2) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_991_test : cos(307*pi/2)=sin(-pi/2) * sin(2*pi) + cos(-pi/2) * cos(2*pi):=
begin
have : cos(-5*pi/2) = cos(307*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-5*pi/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/2) = sin(-pi/2) * sin(2*pi) + cos(-pi/2) * cos(2*pi),
{
have : cos(-5*pi/2) = cos((-pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_992_test : cos(157*pi/2)=cos(179*pi/2):=
begin
have : sin(-2*pi) = cos(157*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(179*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_993_test : sin(166*pi)=- sin(165*pi):=
begin
have : sin(2*pi) = sin(166*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(165*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_994_test (h0 : tan(775*pi/12)≠ 0) : -1/tan(775*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / tan(775 * pi / 12) = -1/tan(775*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(775*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_995_test : cos(pi/6)=sin(458*pi/3):=
begin
have : - -sin(458 * pi / 3) = sin(458*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(167*pi/3) = -sin(458*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (167*pi/3) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = - sin(167*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_996_test (h0 : cos(-pi/3)≠ 0) : -sin(169*pi/3)/cos(-pi/3)=tan(-pi/3):=
begin
have : sin(-pi/3) = -sin(169*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_997_test : -cos(2077*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(2077*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_998_test : -cos(991*pi/6)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -cos(991*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end




lemma Trigo_1000_test : -sin(351*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -sin(351*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/4) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_1001_test (h0 : tan(89*pi/6)≠ 0) : -1/tan(89*pi/6)=sqrt( 3 ):=
begin
have : (-1) / tan(89 * pi / 6) = -1/tan(89*pi/6),
{
field_simp at *,
},
have : tan(pi/3) = -1 / tan(89*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_1002_test : -sin(179*pi/2)=cos(146*pi):=
begin
have : cos(2*pi) = -sin(179*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(146*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1003_test : cos(pi) * cos(-2*pi)=cos(pi)*cos(2*pi):=
begin
have : 1 / 2 * (2 * cos(2 * pi) * cos(pi)) = cos(pi)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi) + cos(-pi) = 2 * cos(2*pi) * cos(pi),
{
rw cos_add_cos,
have : cos(((3*pi) + (-pi))/2) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((3*pi) - (-pi))/2) = cos(2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(3*pi) + cos(-pi)) = cos(3*pi)/2+cos(-pi)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : cos(pi) * cos(-2*pi) = cos(3*pi) / 2 + cos(-pi) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (-2*pi)) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (-2*pi)) = cos(3*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1004_test : sin(-pi)**2 + (cos(-5*pi/6)*cos(pi/6) + sin(-5*pi/6)*sin(pi/6))**2=1:=
begin
have : sin(-pi) ** 2 + (sin((-5) * pi / 6) * sin(pi / 6) + cos((-5) * pi / 6) * cos(pi / 6)) ** 2 = sin(-pi)**2 + (cos(-5*pi/6)*cos(pi/6) + sin(-5*pi/6)*sin(pi/6))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(-5*pi/6) * sin(pi/6) + cos(-5*pi/6) * cos(pi/6),
{
have : cos(-pi) = cos((-5*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) ** 2 + cos(-pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_1005_test : -cos(9*pi)=cos(42*pi):=
begin
have : cos(-2*pi) = -cos(9*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(42*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1006_test : 2*sin(-pi)*cos(-pi)=- sin(126*pi):=
begin
have : sin(-pi) * cos(-pi) + sin(-pi) * cos(-pi) = 2*sin(-pi)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-pi) * cos(-pi) + sin(-pi) * cos(-pi),
{
have : sin(-2*pi) = sin((-pi) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(126*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1007_test : cos(589*pi/6)=sin(499*pi/3):=
begin
have : sin(pi/3) = cos(589*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(499*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1008_test : cos(59*pi/3)=1 / 2:=
begin
have : sin(pi/6) = cos(59*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_1009_test : sin(147*pi/2)*cos(-pi/2)=cos(3*pi/2) / 2 + cos(pi/2) / 2:=
begin
have : cos(pi) = sin(147*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * cos(-pi/2) = cos(3*pi/2) / 2 + cos(pi/2) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (-pi/2)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (-pi/2)) = cos(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1010_test : cos(-pi)=sin(195*pi/2):=
begin
have : - -sin(195 * pi / 2) = sin(195*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(185*pi/2) = -sin(195*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (185*pi/2) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = - sin(185*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1011_test : sin(pi) + sin(-pi)=-2*sin(0)*cos(164*pi):=
begin
have : 2 * sin(0) * -cos(164 * pi) = -2*sin(0)*cos(164*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -cos(164*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) + sin(-pi) = 2 * sin(0) * cos(pi),
{
rw sin_add_sin,
have : sin(((pi) + (-pi))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (-pi))/2) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1012_test : -sin(169*pi/3)=2 * sin(-pi/6) * cos(-pi/6):=
begin
have : sin(-pi/3) = -sin(169*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = 2 * sin(-pi/6) * cos(-pi/6),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_1013_test : sin(-8*pi/3)*cos(pi/3) - sin(pi/3)*cos(-8*pi/3)=- 4 * sin(-pi) ** 3 + 3 * sin(-pi):=
begin
have : sin((-8) * pi / 3) * cos(pi / 3) - sin(pi / 3) * cos((-8) * pi / 3) = sin(-8*pi/3)*cos(pi/3) - sin(pi/3)*cos(-8*pi/3),
{
field_simp at *,
},
have : sin(-3*pi) = sin(-8*pi/3) * cos(pi/3) - sin(pi/3) * cos(-8*pi/3),
{
have : sin(-3*pi) = sin((-8*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi) = - 4 * sin(-pi) ** 3 + 3 * sin(-pi),
{
have : sin(-3*pi) = sin(3*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_1014_test (h0 : tan(407*pi/6)≠ 0) : 1/tan(407*pi/6)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = 1 / tan(407*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_1015_test : -sin(74*pi)=4 * cos(-pi/2) ** 3 - 3 * cos(-pi/2):=
begin
have : cos(-3*pi/2) = -sin(74*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/2) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = 4 * cos(-pi/2) ** 3 - 3 * cos(-pi/2),
{
have : cos(-3*pi/2) = cos(3*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_1016_test : -tan(75*pi)=0:=
begin
have : tan(pi) = -tan(75*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end




lemma Trigo_1018_test : sin(pi/2) ** 2=1/2 - sin(111*pi/2)/2:=
begin
have : cos(pi) = sin(111*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) ** 2 = 1 / 2 - cos(pi) / 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end






lemma Trigo_1022_test : -tan(56*pi)=- tan(35*pi):=
begin
have : tan(2*pi) = -tan(56*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - tan(35*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1023_test : -3*cos(pi/9) + 4*cos(pi/9)**3=sin(pi/6) * sin(-pi/6) + cos(pi/6) * cos(-pi/6):=
begin
have : 4 * cos(pi / 9) ** 3 - 3 * cos(pi / 9) = -3*cos(pi/9) + 4*cos(pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 4 * cos(pi/9) ** 3 - 3 * cos(pi/9),
{
have : cos(pi/3) = cos(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(pi/6) * sin(-pi/6) + cos(pi/6) * cos(-pi/6),
{
have : cos(pi/3) = cos((pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end




lemma Trigo_1025_test : sin(21*pi/2)**2=1 - sin(2*pi) ** 2:=
begin
have : cos(2*pi) = sin(21*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) ** 2 = 1 - sin(2*pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_1026_test : sin(40*pi)**2=1 / 2 - cos(-2*pi) / 2:=
begin
have : (-sin(40 * pi)) ** 2 = sin(40*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -sin(40*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) ** 2 = 1 / 2 - cos(-2*pi) / 2,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_1027_test (h0 : cos(-pi/6)≠ 0) : sin(-pi/6)/cos(-pi/6)=- 1 / tan(34*pi/3):=
begin
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - 1 / tan(34*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1028_test : sin(0)=(sin(pi/6)*cos(pi/3) + sin(pi/3)*cos(pi/6))*cos(-pi/2) + sin(-pi/2)*cos(pi/2):=
begin
have : sin(-pi / 2) * cos(pi / 2) + (sin(pi / 3) * cos(pi / 6) + sin(pi / 6) * cos(pi / 3)) * cos(-pi / 2) = (sin(pi/6)*cos(pi/3) + sin(pi/3)*cos(pi/6))*cos(-pi/2) + sin(-pi/2)*cos(pi/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(pi/3) * cos(pi/6) + sin(pi/6) * cos(pi/3),
{
have : sin(pi/2) = sin((pi/3) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(0) = sin(-pi/2) * cos(pi/2) + sin(pi/2) * cos(-pi/2),
{
have : sin(0) = sin((-pi/2) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end




lemma Trigo_1030_test : -tan(251*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(251*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_1031_test : sin(5*pi/3)=sin(-pi/3)*cos(-2*pi) + sin(-2*pi)*cos(170*pi/3):=
begin
have : sin(-pi / 3) * cos((-2) * pi) - sin((-2) * pi) * -cos(170 * pi / 3) = sin(-pi/3)*cos(-2*pi) + sin(-2*pi)*cos(170*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -cos(170*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/3) = sin(-pi/3) * cos(-2*pi) - sin(-2*pi) * cos(-pi/3),
{
have : sin(5*pi/3) = sin((-pi/3) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_1032_test : sin(65*pi/6)=- sin(pi/6) ** 2 + cos(pi/6) ** 2:=
begin
have : cos(pi/3) = sin(65*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - sin(pi/6) ** 2 + cos(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end






lemma Trigo_1035_test : (sin(-4*pi/3)*sin(-pi/3) + cos(-4*pi/3)*cos(-pi/3))*cos(pi/6)=cos(7*pi/6) / 2 + cos(-5*pi/6) / 2:=
begin
have : cos(pi / 6) * (sin((-4) * pi / 3) * sin(-pi / 3) + cos((-4) * pi / 3) * cos(-pi / 3)) = (sin(-4*pi/3)*sin(-pi/3) + cos(-4*pi/3)*cos(-pi/3))*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(-4*pi/3) * sin(-pi/3) + cos(-4*pi/3) * cos(-pi/3),
{
have : cos(-pi) = cos((-4*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) * cos(-pi) = cos(7*pi/6) / 2 + cos(-5*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((pi/6) + (-pi)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (-pi)) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1036_test : -cos(755*pi/6)=sin(pi/6) * cos(-pi/2) + sin(-pi/2) * cos(pi/6):=
begin
have : sin(-pi/3) = -cos(755*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(pi/6) * cos(-pi/2) + sin(-pi/2) * cos(pi/6),
{
have : sin(-pi/3) = sin((pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end








lemma Trigo_1040_test : -cos(174*pi)=- sin(-2*pi) * sin(-pi) + cos(-2*pi) * cos(-pi):=
begin
have : cos(-3*pi) = -cos(174*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-3*pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi) = - sin(-2*pi) * sin(-pi) + cos(-2*pi) * cos(-pi),
{
have : cos(-3*pi) = cos((-2*pi) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_1041_test : -sin(1043*pi/6)=1 / 2:=
begin
have : sin(pi/6) = -sin(1043*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_1042_test : 2*sin(pi/6)*cos(pi/6)=sin(602*pi/3):=
begin
have : sin(pi/3) = 2 * sin(pi/6) * cos(pi/6),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(602*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1043_test (h0 : tan(69*pi/2)≠ 0) : 1/tan(69*pi/2)=tan(42*pi):=
begin
have : tan(-pi) = 1 / tan(69*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(42*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1044_test (h0 : cos(0)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (tan(0)*tan(-pi/3)+1)≠ 0) (h3 : (1+tan(0)*tan(-pi/3))≠ 0) : sin(pi/3) / cos(pi/3)=(tan(0) - tan(-pi/3))/(tan(0)*tan(-pi/3) + 1):=
begin
have : (tan(0) - tan(-pi / 3)) / (1 + tan(0) * tan(-pi / 3)) = (tan(0) - tan(-pi/3))/(tan(0)*tan(-pi/3) + 1),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = ( tan(0) - tan(-pi/3) ) / ( 1 + tan(0) * tan(-pi/3) ),
{
have : tan(pi/3) = tan((0) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_1045_test : -sin(61*pi/3)=cos(19*pi/6):=
begin
have : sin(-pi/3) = -sin(61*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(19*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1046_test : -2*sin(-pi/12)**2 + cos(-pi/3) + 1=2 * cos(pi/12) * cos(-pi/4):=
begin
have : 1 - 2 * sin(-pi / 12) ** 2 + cos(-pi / 3) = -2*sin(-pi/12)**2 + cos(-pi/3) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = 1 - 2 * sin(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) + cos(-pi/3) = 2 * cos(pi/12) * cos(-pi/4),
{
rw cos_add_cos,
have : cos(((-pi/6) + (-pi/3))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (-pi/3))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1047_test : cos(-pi/6)*cos(pi/2) - sin(-pi/6)*sin(pi/2)=- sin(pi/6) ** 2 + cos(pi/6) ** 2:=
begin
have : -sin(pi / 2) * sin(-pi / 6) + cos(pi / 2) * cos(-pi / 6) = cos(-pi/6)*cos(pi/2) - sin(-pi/6)*sin(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(pi/2) * sin(-pi/6) + cos(pi/2) * cos(-pi/6),
{
have : cos(pi/3) = cos((pi/2) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - sin(pi/6) ** 2 + cos(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end




lemma Trigo_1049_test : sin(-3*pi/2)=-sin(2*pi)*cos(pi/2) + (cos(-pi/3)*cos(5*pi/3) + sin(-pi/3)*sin(5*pi/3))*sin(pi/2):=
begin
have : sin(pi / 2) * (sin(5 * pi / 3) * sin(-pi / 3) + cos(5 * pi / 3) * cos(-pi / 3)) - sin(2 * pi) * cos(pi / 2) = -sin(2*pi)*cos(pi/2) + (cos(-pi/3)*cos(5*pi/3) + sin(-pi/3)*sin(5*pi/3))*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(5*pi/3) * sin(-pi/3) + cos(5*pi/3) * cos(-pi/3),
{
have : cos(2*pi) = cos((5*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/2) = sin(pi/2) * cos(2*pi) - sin(2*pi) * cos(pi/2),
{
have : sin(-3*pi/2) = sin((pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_1050_test : tan(241*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(pi/12) = tan(241*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_1051_test : sin(-pi/3)*sin(pi/6) + cos(-pi/3)*cos(pi/6)=cos(101*pi/2):=
begin
have : sin(pi / 6) * sin(-pi / 3) + cos(pi / 6) * cos(-pi / 3) = sin(-pi/3)*sin(pi/6) + cos(-pi/3)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(pi/6) * sin(-pi/3) + cos(pi/6) * cos(-pi/3),
{
have : cos(pi/2) = cos((pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(101*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1052_test (h0 : cos(-pi/2)≠ 0) (h1 : (4*cos(-pi/2)**2)≠ 0) (h2 : (2*cos(-pi/2))≠ 0) : cos(-pi/2)**2 + sin(-pi)**2/(4*cos(-pi/2)**2)=1:=
begin
have : (sin(-pi) / (2 * cos(-pi / 2))) ** 2 + cos(-pi / 2) ** 2 = cos(-pi/2)**2 + sin(-pi)**2/(4*cos(-pi/2)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-pi) / ( 2 * cos(-pi/2) ),
{
have : sin(-pi) = sin(2*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) ** 2 + cos(-pi/2) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_1053_test : -cos(367*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -cos(367*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3*pi/4) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_1054_test : cos(211*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = cos(211*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_1055_test : -cos(445*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(445*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end






lemma Trigo_1058_test : cos(317*pi/2)=sin(190*pi):=
begin
have : sin(-2*pi) = cos(317*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(190*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1059_test (h0 : cos(104*pi)≠ 0) : tan(-2*pi)=sin(-2*pi)/cos(104*pi):=
begin
have : sin((-2) * pi) / cos(104 * pi) = sin(-2*pi)/cos(104*pi),
{
field_simp at *,
},
have : cos(-2*pi) = cos(104*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_1061_test : -sin(-pi/3)*cos(365*pi/6)=cos(2*pi/3) / 2 - cos(0) / 2:=
begin
have : -cos(365 * pi / 6) * sin(-pi / 3) = -sin(-pi/3)*cos(365*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(365*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * sin(-pi/3) = cos(2*pi/3) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
have : cos((pi/3) + (-pi/3)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (-pi/3)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_1063_test : -cos(329*pi/2)=- sin(6*pi):=
begin
have : sin(-pi) = -cos(329*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(6*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1064_test : cos(pi/3) + cos(82*pi)=2 * cos(-7*pi/6) * cos(-5*pi/6):=
begin
have : cos(82 * pi) + cos(pi / 3) = cos(pi/3) + cos(82*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(82*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(pi/3) = 2 * cos(-7*pi/6) * cos(-5*pi/6),
{
rw cos_add_cos,
have : cos(((-2*pi) + (pi/3))/2) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi/3))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1065_test : cos(-pi/2)=-2*sin(-pi/3)*sin(-pi/12)*cos(-pi/12) + cos(-pi/3)*cos(-pi/6):=
begin
have : -sin(-pi / 3) * (2 * sin(-pi / 12) * cos(-pi / 12)) + cos(-pi / 3) * cos(-pi / 6) = -2*sin(-pi/3)*sin(-pi/12)*cos(-pi/12) + cos(-pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = 2 * sin(-pi/12) * cos(-pi/12),
{
have : sin(-pi/6) = sin(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(-pi/3) * sin(-pi/6) + cos(-pi/3) * cos(-pi/6),
{
have : cos(-pi/2) = cos((-pi/3) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw ← this,
end


lemma Trigo_1066_test : sin(76*pi)*cos(-pi)=cos(-3*pi/2) / 2 + cos(-pi/2) / 2:=
begin
have : cos(-pi) * sin(76 * pi) = sin(76*pi)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(76*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(pi/2) = cos(-3*pi/2) / 2 + cos(-pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (pi/2)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (pi/2)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_1068_test : sin(2*pi)*sin(6*pi) + cos(2*pi)*cos(6*pi)=2 * cos(2*pi) ** 2 - 1:=
begin
have : sin(6 * pi) * sin(2 * pi) + cos(6 * pi) * cos(2 * pi) = sin(2*pi)*sin(6*pi) + cos(2*pi)*cos(6*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = sin(6*pi) * sin(2*pi) + cos(6*pi) * cos(2*pi),
{
have : cos(4*pi) = cos((6*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = 2 * cos(2*pi) ** 2 - 1,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_1069_test : sin(-7*pi/3)=-(-1 + 2*cos(-pi)**2)*sin(pi/3) + sin(-2*pi)*cos(pi/3):=
begin
have : sin((-2) * pi) * cos(pi / 3) - sin(pi / 3) * (2 * cos(-pi) ** 2 - 1) = -(-1 + 2*cos(-pi)**2)*sin(pi/3) + sin(-2*pi)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = 2 * cos(-pi) ** 2 - 1,
{
have : cos(-2*pi) = cos(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-7*pi/3) = sin(-2*pi) * cos(pi/3) - sin(pi/3) * cos(-2*pi),
{
have : sin(-7*pi/3) = sin((-2*pi) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_1070_test : cos(-2*pi) * cos(pi/6)=cos(-2*pi)*cos(-pi/6):=
begin
have : 1 / 2 * (2 * cos(-pi / 6) * cos((-2) * pi)) = cos(-2*pi)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-13*pi/6) + cos(-11*pi/6) = 2 * cos(-pi/6) * cos(-2*pi),
{
rw cos_add_cos,
have : cos(((-13*pi/6) + (-11*pi/6))/2) = cos(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-13*pi/6) - (-11*pi/6))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(-13*pi/6) + cos(-11*pi/6)) = cos(-13*pi/6)/2+cos(-11*pi/6)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-2*pi) * cos(pi/6) = cos(-13*pi/6) / 2 + cos(-11*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (pi/6)) = cos(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/6)) = cos(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1071_test (h0 : cos(-pi/12)≠ 0) (h1 : (1-tan(-pi/12)**2)≠ 0) : 2*tan(-pi/12)/(1 - tan(-pi/12)**2)=- 1 / tan(49*pi/3):=
begin
have : tan(-pi/6) = 2 * tan(-pi/12) / ( 1 - tan(-pi/12) ** 2 ),
{
have : tan(-pi/6) = tan(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - 1 / tan(49*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1072_test (h0 : tan(59*pi/6)≠ 0) : -1/tan(59*pi/6)=sqrt( 3 ):=
begin
have : (-1) / tan(59 * pi / 6) = -1/tan(59*pi/6),
{
field_simp at *,
},
have : tan(pi/3) = -1 / tan(59*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_1073_test : sin(-pi/2) ** 2=1 - sin(86*pi)**2:=
begin
have : cos(-pi/2) = sin(86*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) ** 2 = 1 - cos(-pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_1074_test : cos(136*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(136*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_1075_test : -cos(118*pi)=- sin(37*pi/2):=
begin
have : cos(-pi) = -cos(118*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(37*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1077_test : sin(67*pi)=0:=
begin
have : cos(pi/2) = sin(67*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end




lemma Trigo_1079_test : -cos(2*pi/3)=- cos(4*pi/3):=
begin
have : cos(-pi/3) = -cos(2*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(4*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1080_test : cos(-pi/2)=sin(215*pi/3)*cos(-pi/3) - sin(-pi/3)*cos(215*pi/3):=
begin
have : sin(72*pi) = sin(215*pi/3) * cos(-pi/3) - sin(-pi/3) * cos(215*pi/3),
{
have : sin(72*pi) = sin((215*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(72*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1081_test : sin(262*pi/3)=- cos(589*pi/6):=
begin
have : sin(-pi/3) = sin(262*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - cos(589*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1082_test : cos(739*pi/6)**2=1 - cos(-pi/3) ** 2:=
begin
have : sin(-pi/3) = cos(739*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) ** 2 = 1 - cos(-pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_1083_test : cos(120*pi)=1:=
begin
have : sin(pi/2) = cos(120*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_1084_test : tan(49*pi/4)=1:=
begin
have : tan(pi/4) = tan(49*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (pi/4) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_1085_test : -sin(1037*pi/6)=- sin(109*pi/6):=
begin
have : sin(-pi/6) = -sin(1037*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(109*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1086_test : sin(pi/6) ** 2=1 - (1 - 2*sin(pi/12)**2)**2:=
begin
have : cos(pi/6) = 1 - 2 * sin(pi/12) ** 2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 - cos(pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_1087_test : -sin(183*pi)=0:=
begin
have : cos(pi/2) = -sin(183*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_1088_test : cos(1007*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(1007*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_1089_test : -cos(230*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(230*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_1090_test : cos(257*pi/3)=1 / 2:=
begin
have : sin(pi/6) = cos(257*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_1091_test : -cos(829*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(829*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_1092_test : sin(-4*pi)=2*(cos(-5*pi/3)*cos(-pi/3) - sin(-5*pi/3)*sin(-pi/3))*sin(-2*pi):=
begin
have : 2 * sin((-2) * pi) * (-sin((-5) * pi / 3) * sin(-pi / 3) + cos((-5) * pi / 3) * cos(-pi / 3)) = 2*(cos(-5*pi/3)*cos(-pi/3) - sin(-5*pi/3)*sin(-pi/3))*sin(-2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -sin(-5*pi/3) * sin(-pi/3) + cos(-5*pi/3) * cos(-pi/3),
{
have : cos(-2*pi) = cos((-5*pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-4*pi) = 2 * sin(-2*pi) * cos(-2*pi),
{
have : sin(-4*pi) = sin(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_1093_test : tan(55*pi)=- 1 / tan(25*pi/2):=
begin
have : tan(pi) = tan(55*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(25*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1094_test : sin(817*pi/6)*cos(-pi/6)=cos(pi/2) / 2 + cos(pi/6) / 2:=
begin
have : cos(pi/3) = sin(817*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) * cos(-pi/6) = cos(pi/2) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
have : cos((pi/3) + (-pi/6)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (-pi/6)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1095_test (h0 : cos(pi/6)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(pi/6)*tan(-pi/3))≠ 0) (h3 : (tan(-pi/3)*tan(pi/6)+1)≠ 0) : (tan(pi/6) - tan(-pi/3))/(tan(-pi/3)*tan(pi/6) + 1)=tan(201*pi/2):=
begin
have : (tan(pi / 6) - tan(-pi / 3)) / (1 + tan(pi / 6) * tan(-pi / 3)) = (tan(pi/6) - tan(-pi/3))/(tan(-pi/3)*tan(pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = ( tan(pi/6) - tan(-pi/3) ) / ( 1 + tan(pi/6) * tan(-pi/3) ),
{
have : tan(pi/2) = tan((pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = tan(201*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1096_test : cos(-4*pi)=-sin(-2*pi)*sin(85*pi) + cos(-2*pi)*cos(2*pi):=
begin
have : sin((-2) * pi) * -sin(85 * pi) + cos((-2) * pi) * cos(2 * pi) = -sin(-2*pi)*sin(85*pi) + cos(-2*pi)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -sin(85*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi) = sin(-2*pi) * sin(2*pi) + cos(-2*pi) * cos(2*pi),
{
have : cos(-4*pi) = cos((-2*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end






lemma Trigo_1099_test : sin(-pi/6) - sin(-pi)=2*sin(5*pi/12)*sin(2231*pi/12):=
begin
have : cos(-7*pi/12) = sin(2231*pi/12),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-7*pi/12) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) - sin(-pi) = 2 * sin(5*pi/12) * cos(-7*pi/12),
{
rw sin_sub_sin,
have : cos(((-pi/6) + (-pi))/2) = cos(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (-pi))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1100_test (h0 : cos(-2*pi)≠ 0) (h1 : (2*cos(64*pi))≠ 0) : sin(-2*pi)=sin(-4*pi)/(2*cos(64*pi)):=
begin
have : sin((-4) * pi) / (2 * cos(64 * pi)) = sin(-4*pi)/(2*cos(64*pi)),
{
field_simp at *,
},
have : cos(-2*pi) = cos(64*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = sin(-4*pi) / ( 2 * cos(-2*pi) ),
{
have : sin(-4*pi) = sin(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
rw this,
end


lemma Trigo_1101_test : sin(169*pi)=- cos(315*pi/2):=
begin
have : cos(-pi/2) = sin(169*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(315*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1102_test : sin(130*pi) + cos(pi/3)=2 * cos(5*pi/12) * cos(-pi/12):=
begin
have : cos(pi / 3) + sin(130 * pi) = sin(130*pi) + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(130*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) + cos(-pi/2) = 2 * cos(5*pi/12) * cos(-pi/12),
{
rw cos_add_cos,
have : cos(((pi/3) + (-pi/2))/2) = cos(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (-pi/2))/2) = cos(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1103_test : cos(75*pi/2)=cos(169*pi/2):=
begin
have : sin(pi) = cos(75*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(169*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1104_test : cos(pi/3)=cos(-pi/2)*cos(-pi/6) + 2*sin(-pi/2)*sin(-pi/12)*cos(-pi/12):=
begin
have : 2 * sin(-pi / 12) * cos(-pi / 12) * sin(-pi / 2) + cos(-pi / 6) * cos(-pi / 2) = cos(-pi/2)*cos(-pi/6) + 2*sin(-pi/2)*sin(-pi/12)*cos(-pi/12),
{
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = 2 * sin(-pi/12) * cos(-pi/12),
{
have : sin(-pi/6) = sin(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(-pi/6) * sin(-pi/2) + cos(-pi/6) * cos(-pi/2),
{
have : cos(pi/3) = cos((-pi/6) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_1105_test : -tan(181*pi/2)=tan(155*pi/2):=
begin
have : tan(-pi/2) = -tan(181*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = tan(155*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1106_test : cos(817*pi/6)=- sin(437*pi/3):=
begin
have : cos(-pi/6) = cos(817*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - sin(437*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1108_test : cos(pi/3)=-cos(260*pi/3)**2 + cos(pi/6)**2:=
begin
have : -(-cos(260 * pi / 3)) ** 2 + cos(pi / 6) ** 2 = -cos(260*pi/3)**2 + cos(pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -cos(260*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = - sin(pi/6) ** 2 + cos(pi/6) ** 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_1109_test : -sin(859*pi/6)=- cos(296*pi/3):=
begin
have : cos(-pi/3) = -sin(859*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(296*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1111_test : cos(433*pi/3)=2 * cos(pi/6) ** 2 - 1:=
begin
have : cos(pi/3) = cos(433*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 2 * cos(pi/6) ** 2 - 1,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_1112_test : -sin(pi/6) + sin(11*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(11*pi/6)=2 * sin(11*pi/12) * cos(13*pi/12):=
begin
have : sin(11 * pi / 6) * cos(-pi / 6) - sin(-pi / 6) * cos(11 * pi / 6) - sin(pi / 6) = -sin(pi/6) + sin(11*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(11*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(11*pi/6) * cos(-pi/6) - sin(-pi/6) * cos(11*pi/6),
{
have : sin(2*pi) = sin((11*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) - sin(pi/6) = 2 * sin(11*pi/12) * cos(13*pi/12),
{
rw sin_sub_sin,
have : cos(((2*pi) + (pi/6))/2) = cos(13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi) - (pi/6))/2) = sin(11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1113_test : sin(2*pi)=sin(-pi/6)*sin(296*pi/3) - cos(-pi/6)*cos(296*pi/3):=
begin
have : -(-sin(296 * pi / 3) * sin(-pi / 6) + cos(296 * pi / 3) * cos(-pi / 6)) = sin(-pi/6)*sin(296*pi/3) - cos(-pi/6)*cos(296*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(197*pi/2) = -sin(296*pi/3) * sin(-pi/6) + cos(296*pi/3) * cos(-pi/6),
{
have : cos(197*pi/2) = cos((296*pi/3) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = - cos(197*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1115_test : -cos(386*pi/3)=sin(49*pi/6):=
begin
have : sin(pi/6) = -cos(386*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(49*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1116_test : cos(55*pi/3)=cos(485*pi/3):=
begin
have : cos(pi/3) = cos(55*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(485*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1117_test : cos(-pi/6)=cos(1045*pi/6):=
begin
have : - -cos(1045 * pi / 6) = cos(1045*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(52*pi/3) = -cos(1045*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (52*pi/3) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(52*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1119_test : cos(-pi/6)=cos(577*pi/6):=
begin
have : sin(50*pi/3) = cos(577*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (50*pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(50*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1120_test : -cos(135*pi)=- cos(111*pi):=
begin
have : cos(-2*pi) = -cos(135*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - cos(111*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1121_test : -3*cos(-pi/9) + 4*cos(-pi/9)**3=cos(463*pi/3):=
begin
have : 4 * cos(-pi / 9) ** 3 - 3 * cos(-pi / 9) = -3*cos(-pi/9) + 4*cos(-pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = 4 * cos(-pi/9) ** 3 - 3 * cos(-pi/9),
{
have : cos(-pi/3) = cos(3*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(463*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1122_test : sin(pi/6)=1 - 2*cos(220*pi/3)**2:=
begin
have : -(2 * cos(220 * pi / 3) ** 2 - 1) = 1 - 2*cos(220*pi/3)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(440*pi/3) = 2 * cos(220*pi/3) ** 2 - 1,
{
have : cos(440*pi/3) = cos(2*(220*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(440*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1123_test : -sin(379*pi/2)=1:=
begin
have : sin(pi/2) = -sin(379*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_1124_test : sin(pi/6)=-4*cos(266*pi/9)**3 + 3*cos(266*pi/9):=
begin
have : -(4 * cos(266 * pi / 9) ** 3 - 3 * cos(266 * pi / 9)) = -4*cos(266*pi/9)**3 + 3*cos(266*pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(266*pi/3) = 4 * cos(266*pi/9) ** 3 - 3 * cos(266*pi/9),
{
have : cos(266*pi/3) = cos(3*(266*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(266*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1125_test : cos(35*pi/3)=1 / 2:=
begin
have : cos(pi/3) = cos(35*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_1126_test : -sin(46*pi/3)=2 * sin(pi/6) * cos(pi/6):=
begin
have : sin(pi/3) = -sin(46*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = 2 * sin(pi/6) * cos(pi/6),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end






lemma Trigo_1129_test (h0 : cos(pi)≠ 0) : sin(pi)/cos(pi)=- 1 / tan(93*pi/2):=
begin
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(93*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1130_test : -sin(3*pi)=0:=
begin
have : cos(pi/2) = -sin(3*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_1131_test : sin(197*pi/2)**2=cos(2*pi) / 2 + 1 / 2:=
begin
have : (-sin(197 * pi / 2)) ** 2 = sin(197*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(197*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) ** 2 = cos(2*pi) / 2 + 1 / 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
rw this,
end




lemma Trigo_1133_test : sin(-13*pi/6)*cos(pi/6) + sin(pi/6)*cos(-13*pi/6)=2 * sin(-pi) * cos(-pi):=
begin
have : sin((-13) * pi / 6) * cos(pi / 6) + sin(pi / 6) * cos((-13) * pi / 6) = sin(-13*pi/6)*cos(pi/6) + sin(pi/6)*cos(-13*pi/6),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-13*pi/6) * cos(pi/6) + sin(pi/6) * cos(-13*pi/6),
{
have : sin(-2*pi) = sin((-13*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = 2 * sin(-pi) * cos(-pi),
{
have : sin(-2*pi) = sin(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_1134_test : cos(119*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = cos(119*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_1135_test : 1/2 - cos(2*pi/3)/2=1 - cos(pi/3) ** 2:=
begin
have : sin(pi/3) ** 2 = 1 / 2 - cos(2*pi/3) / 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 = 1 - cos(pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end




lemma Trigo_1137_test : cos(2*pi) - cos(-pi/3)=2*sin(5*pi/6)*cos(217*pi/3):=
begin
have : (-2) * -cos(217 * pi / 3) * sin(5 * pi / 6) = 2*sin(5*pi/6)*cos(217*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(7*pi/6) = -cos(217*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) - cos(-pi/3) = - 2 * sin(7*pi/6) * sin(5*pi/6),
{
rw cos_sub_cos,
have : sin(((2*pi) + (-pi/3))/2) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi) - (-pi/3))/2) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1138_test : sin(2*pi/3)=-sin(pi)*cos(134*pi/3) - sin(pi/3)*cos(pi):=
begin
have : sin(pi) * -cos(134 * pi / 3) - sin(pi / 3) * cos(pi) = -sin(pi)*cos(134*pi/3) - sin(pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(134*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) = sin(pi) * cos(pi/3) - sin(pi/3) * cos(pi),
{
have : sin(2*pi/3) = sin((pi) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_1139_test (h0 : tan(100*pi/3)≠ 0) : -1/tan(100*pi/3)=tan(299*pi/6):=
begin
have : (-1) / tan(100 * pi / 3) = -1/tan(100*pi/3),
{
field_simp at *,
},
have : tan(-pi/6) = -1 / tan(100*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = tan(299*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1140_test : cos(pi/2)=sin(130*pi):=
begin
have : - -sin(130 * pi) = sin(130*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(113*pi) = -sin(130*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (113*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(113*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1141_test : sin(-pi)=-1 + 2*sin(25*pi/4)**2:=
begin
have : -(1 - 2 * sin(25 * pi / 4) ** 2) = -1 + 2*sin(25*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(25*pi/2) = 1 - 2 * sin(25*pi/4) ** 2,
{
have : cos(25*pi/2) = cos(2*(25*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(25*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1143_test (h0 : tan(142*pi/3)≠ 0) : 1/tan(142*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(142*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_1144_test : cos(281*pi/2)=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : sin(-6*pi) = cos(281*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-6*pi) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-6*pi) = - 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi),
{
have : sin(-6*pi) = sin(3*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_1145_test : cos(575*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = cos(575*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_1146_test : sin(-pi/6)=1 - 2*sin(106*pi/3)**2:=
begin
have : cos(212*pi/3) = 1 - 2 * sin(106*pi/3) ** 2,
{
have : cos(212*pi/3) = cos(2*(106*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = cos(212*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1147_test (h0 : cos(-2*pi)≠ 0) (h1 : (2*cos((-2)*pi))≠ 0) (h2 : (2*cos(-2*pi))≠ 0) : sin(-4*pi)/(2*cos(-2*pi))=cos(175*pi/2):=
begin
have : sin((-4) * pi) / (2 * cos((-2) * pi)) = sin(-4*pi)/(2*cos(-2*pi)),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-4*pi) / ( 2 * cos(-2*pi) ),
{
have : sin(-4*pi) = sin(2*(-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(175*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1148_test : sin(187*pi/6)**2=1 - cos(pi/6) ** 2:=
begin
have : (-sin(187 * pi / 6)) ** 2 = sin(187*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(187*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 - cos(pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_1149_test (h0 : sin(-pi/3)≠ 0) (h1 : (2*sin(-pi/3))≠ 0) : cos(pi) + sin(-2*pi/3)/(2*sin(-pi/3))=2 * cos(2*pi/3) * cos(pi/3):=
begin
have : cos(pi) + sin((-2) * pi / 3) / (2 * sin(-pi / 3)) = cos(pi) + sin(-2*pi/3)/(2*sin(-pi/3)),
{
field_simp at *,
},
have : cos(-pi/3) = sin(-2*pi/3) / ( 2 * sin(-pi/3) ),
{
have : sin(-2*pi/3) = sin(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) + cos(-pi/3) = 2 * cos(2*pi/3) * cos(pi/3),
{
rw cos_add_cos,
have : cos(((pi) + (-pi/3))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (-pi/3))/2) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1150_test (h0 : cos(125*pi/2)≠ 0) : sin(-pi/2)/cos(125*pi/2)=tan(-pi/2):=
begin
have : cos(-pi/2) = cos(125*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) / cos(-pi/2) = tan(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_1151_test : 2*sin(-pi/6)*cos(-pi/6)=sin(335*pi/3):=
begin
have : sin(-pi/3) = 2 * sin(-pi/6) * cos(-pi/6),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(335*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1152_test : sin(130*pi)=0:=
begin
have : sin(pi) = sin(130*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_1153_test (h0 : sin(-pi/6)≠ 0) (h1 : (2*sin(-pi/6))≠ 0) : sin(11*pi/6)=sin(-pi/6)*cos(-2*pi) - sin(-2*pi)*sin(-pi/3)/(2*sin(-pi/6)):=
begin
have : sin(-pi / 6) * cos((-2) * pi) - sin((-2) * pi) * (sin(-pi / 3) / (2 * sin(-pi / 6))) = sin(-pi/6)*cos(-2*pi) - sin(-2*pi)*sin(-pi/3)/(2*sin(-pi/6)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(-pi/3) / ( 2 * sin(-pi/6) ),
{
have : sin(-pi/3) = sin(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(11*pi/6) = sin(-pi/6) * cos(-2*pi) - sin(-2*pi) * cos(-pi/6),
{
have : sin(11*pi/6) = sin((-pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_1154_test : sin(509*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = sin(509*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_1155_test (h0 : cos(-pi)≠ 0) (h1 : (2*-sin(293*pi/2))≠ 0) (h2 : (2*sin(293*pi/2))≠ 0) : sin(-pi)=-sin(-2*pi)/(2*sin(293*pi/2)):=
begin
have : sin((-2) * pi) / (2 * -sin(293 * pi / 2)) = -sin(-2*pi)/(2*sin(293*pi/2)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -sin(293*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = sin(-2*pi) / ( 2 * cos(-pi) ),
{
have : sin(-2*pi) = sin(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
},
rw this,
end


lemma Trigo_1156_test : cos(551*pi/3)=- sin(271*pi/6):=
begin
have : cos(pi/3) = cos(551*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - sin(271*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1157_test : sin(267*pi/2)=- sin(53*pi/2):=
begin
have : sin(-pi/2) = sin(267*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(53*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1158_test : -sin(787*pi/6)=1 / 2:=
begin
have : cos(pi/3) = -sin(787*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_1159_test : -cos(631*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -cos(631*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_1160_test : -cos(440*pi/3)=- sin(539*pi/6):=
begin
have : cos(-pi/3) = -cos(440*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - sin(539*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1162_test : sin(117*pi)=cos(95*pi/2):=
begin
have : sin(2*pi) = sin(117*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(95*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1163_test : sin(-2*pi) + sin(2*pi)=2*(4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(0):=
begin
have : 2 * sin(0) * (4 * cos((-2) * pi / 3) ** 3 - 3 * cos((-2) * pi / 3)) = 2*(4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(0),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = 4 * cos(-2*pi/3) ** 3 - 3 * cos(-2*pi/3),
{
have : cos(-2*pi) = cos(3*(-2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) + sin(2*pi) = 2 * sin(0) * cos(-2*pi),
{
rw sin_add_sin,
have : sin(((-2*pi) + (2*pi))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (2*pi))/2) = cos(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_1165_test : -cos(160*pi/3)=- cos(338*pi/3):=
begin
have : sin(pi/6) = -cos(160*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - cos(338*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1166_test : cos(68*pi/3)**2=1 - sin(pi/3) ** 2:=
begin
have : (-cos(68 * pi / 3)) ** 2 = cos(68*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(68*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) ** 2 = 1 - sin(pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_1167_test : 2*sin(3*pi/2)*cos(3*pi/2)=sin(2*pi) * cos(-pi) - sin(-pi) * cos(2*pi):=
begin
have : sin(3*pi) = 2 * sin(3*pi/2) * cos(3*pi/2),
{
have : sin(3*pi) = sin(2*(3*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) = sin(2*pi) * cos(-pi) - sin(-pi) * cos(2*pi),
{
have : sin(3*pi) = sin((2*pi) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw ← this,
end


lemma Trigo_1168_test : -sin(41*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -sin(41*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_1169_test : -sin(923*pi/6)=cos(457*pi/3):=
begin
have : sin(pi/6) = -sin(923*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(457*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1170_test : sin(127*pi/2)**2=1 - sin(-pi) ** 2:=
begin
have : cos(-pi) = sin(127*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) ** 2 = 1 - sin(-pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_1171_test (h0 : cos(-pi/3)≠ 0) : sin(-pi/3)/cos(-pi/3)=tan(230*pi/3):=
begin
have : tan(-pi/3) = sin(-pi/3) / cos(-pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = tan(230*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (-pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1172_test : cos(pi/2)=sin(114*pi):=
begin
have : - -sin(114 * pi) = sin(114*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(27*pi) = -sin(114*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (27*pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(27*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1173_test : -sin(107*pi)=0:=
begin
have : cos(pi/2) = -sin(107*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_1174_test : cos(pi)=1 - 2*cos(8*pi)**2:=
begin
have : sin(pi/2) = cos(8*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = 1 - 2 * sin(pi/2) ** 2,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_1175_test (h0 : tan(195*pi/2)≠ 0) : 1/tan(195*pi/2)=tan(23*pi):=
begin
have : tan(-2*pi) = 1 / tan(195*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-2*pi) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = tan(23*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1176_test : sin(-pi) * sin(pi/2)=2*cos(-pi/2)**3 - 2*cos(-pi/2):=
begin
have : (4 * cos(-pi / 2) ** 3 - 3 * cos(-pi / 2)) / 2 - cos(-pi / 2) / 2 = 2*cos(-pi/2)**3 - 2*cos(-pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-3*pi/2) = 4 * cos(-pi/2) ** 3 - 3 * cos(-pi/2),
{
have : cos(-3*pi/2) = cos(3*(-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) * sin(pi/2) = cos(-3*pi/2) / 2 - cos(-pi/2) / 2,
{
rw sin_mul_sin,
have : cos((-pi) + (pi/2)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (pi/2)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_1178_test : (sin(0)*sin(-pi/6) + cos(0)*cos(-pi/6))**2=cos(pi/3) / 2 + 1 / 2:=
begin
have : cos(pi/6) = sin(0) * sin(-pi/6) + cos(0) * cos(-pi/6),
{
have : cos(pi/6) = cos((0) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) ** 2 = cos(pi/3) / 2 + 1 / 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_1179_test (h0 : tan(165*pi/4)≠ 0) : 1/tan(165*pi/4)=1:=
begin
have : tan(pi/4) = 1 / tan(165*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_1180_test : sin(191*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = sin(191*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_1181_test : sin(335*pi/2)*cos(pi/6)=cos(-7*pi/6) / 2 + cos(-5*pi/6) / 2:=
begin
have : cos(-pi) = sin(335*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(pi/6) = cos(-7*pi/6) / 2 + cos(-5*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (pi/6)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (pi/6)) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1182_test : -sin(601*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -sin(601*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_1183_test (h0 : tan(295*pi/6)≠ 0) : sin(-pi/3) / cos(-pi/3)=-1/tan(295*pi/6):=
begin
have : (-1) / tan(295 * pi / 6) = -1/tan(295*pi/6),
{
field_simp at *,
},
have : tan(-pi/3) = -1 / tan(295*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_1184_test : cos(49*pi/3)=- sin(11*pi/6):=
begin
have : sin(pi/6) = cos(49*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(11*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1185_test (h0 : tan(5*pi/3)≠ 0) : 1/tan(5*pi/3)=tan(389*pi/6):=
begin
have : tan(-pi/6) = 1 / tan(5*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = tan(389*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1186_test : sin(-pi/3)=-cos(899*pi/12)**2 + sin(899*pi/12)**2:=
begin
have : -(-sin(899 * pi / 12) ** 2 + cos(899 * pi / 12) ** 2) = -cos(899*pi/12)**2 + sin(899*pi/12)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(899*pi/6) = -sin(899*pi/12) ** 2 + cos(899*pi/12) ** 2,
{
have : cos(899*pi/6) = cos(2*(899*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = - cos(899*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1187_test : 3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3=- cos(93*pi/2):=
begin
have : (-4) * sin((-2) * pi / 3) ** 3 + 3 * sin((-2) * pi / 3) = 3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -4 * sin(-2*pi/3) ** 3 + 3 * sin(-2*pi/3),
{
have : sin(-2*pi) = sin(3*(-2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - cos(93*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1188_test : -cos(569*pi/6)=- sin(70*pi/3):=
begin
have : cos(-pi/6) = -cos(569*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - sin(70*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1189_test : sin(2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(2*pi)=1 / 2:=
begin
have : sin((-11) * pi / 6) * cos(2 * pi) + sin(2 * pi) * cos((-11) * pi / 6) = sin(2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-11*pi/6) * cos(2*pi) + sin(2*pi) * cos(-11*pi/6),
{
have : sin(pi/6) = sin((-11*pi/6) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_1190_test (h0 : tan(242*pi/3)≠ 0) : -1/tan(242*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(242 * pi / 3) = -1/tan(242*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(242*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end




lemma Trigo_1192_test : 1 - 2*sin(pi/4)**2=- cos(127*pi/2):=
begin
have : cos(pi/2) = 1 - 2 * sin(pi/4) ** 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(127*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1193_test : -sin(889*pi/6)=cos(346*pi/3):=
begin
have : sin(-pi/6) = -sin(889*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(346*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1194_test : sin(pi) - sin(-pi/2)=2*(cos(-pi/2)*cos(-pi/4) + sin(-pi/2)*sin(-pi/4))*sin(3*pi/4):=
begin
have : 2 * sin(3 * pi / 4) * (sin(-pi / 4) * sin(-pi / 2) + cos(-pi / 4) * cos(-pi / 2)) = 2*(cos(-pi/2)*cos(-pi/4) + sin(-pi/2)*sin(-pi/4))*sin(3*pi/4),
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = sin(-pi/4) * sin(-pi/2) + cos(-pi/4) * cos(-pi/2),
{
have : cos(pi/4) = cos((-pi/4) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) - sin(-pi/2) = 2 * sin(3*pi/4) * cos(pi/4),
{
rw sin_sub_sin,
have : cos(((pi) + (-pi/2))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi) - (-pi/2))/2) = sin(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1195_test : cos(-pi/6) ** 2=1 - cos(380*pi/3)**2:=
begin
have : sin(-pi/6) = cos(380*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) ** 2 = 1 - sin(-pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_1196_test : cos(5*pi/6)=cos(pi/6)*cos(pi) + sin(pi)*cos(569*pi/3):=
begin
have : sin(pi) * cos(569 * pi / 3) + cos(pi) * cos(pi / 6) = cos(pi/6)*cos(pi) + sin(pi)*cos(569*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = cos(569*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/6) = sin(pi) * sin(pi/6) + cos(pi) * cos(pi/6),
{
have : cos(5*pi/6) = cos((pi) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_1197_test : cos(58*pi)=cos(158*pi):=
begin
have : cos(2*pi) = cos(58*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(158*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1198_test : -cos(347*pi/2)=- cos(79*pi/2):=
begin
have : cos(-pi/2) = -cos(347*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(79*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1199_test : cos(-pi/3) ** 2=1 - sin(179*pi/3)**2:=
begin
have : sin(-pi/3) = sin(179*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) ** 2 = 1 - sin(-pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_1200_test : sin(pi/6)=sin(-pi/3)*cos(209*pi/2) + sin(pi/2)*cos(-pi/3):=
begin
have : sin(pi / 2) * cos(-pi / 3) + sin(-pi / 3) * cos(209 * pi / 2) = sin(-pi/3)*cos(209*pi/2) + sin(pi/2)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = cos(209*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = sin(pi/2) * cos(-pi/3) + sin(-pi/3) * cos(pi/2),
{
have : sin(pi/6) = sin((pi/2) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw ← this,
end


lemma Trigo_1201_test : -sin(-2*pi)*cos(406*pi/3)=sin(-7*pi/3) / 2 + sin(-5*pi/3) / 2:=
begin
have : sin((-2) * pi) * -cos(406 * pi / 3) = -sin(-2*pi)*cos(406*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(406*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(pi/3) = sin(-7*pi/3) / 2 + sin(-5*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (pi/3)) = sin(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi/3)) = sin(-7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1202_test : -1 + 2*cos(-pi/12)**2=- sin(557*pi/3):=
begin
have : 2 * cos(-pi / 12) ** 2 - 1 = -1 + 2*cos(-pi/12)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = 2 * cos(-pi/12) ** 2 - 1,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - sin(557*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1203_test : cos(2*pi)=sin(169*pi)*cos(-pi/2) + sin(-pi/2)*cos(169*pi):=
begin
have : sin(337*pi/2) = sin(169*pi) * cos(-pi/2) + sin(-pi/2) * cos(169*pi),
{
have : sin(337*pi/2) = sin((169*pi) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(337*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1205_test : sin(439*pi/6)=cos(32*pi/3):=
begin
have : sin(-pi/6) = sin(439*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(32*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1206_test : -1 - cos(pi/2) + 2*cos(-pi/4)**2=- 2 * sin(-pi/2) * sin(0):=
begin
have : 2 * cos(-pi / 4) ** 2 - 1 - cos(pi / 2) = -1 - cos(pi/2) + 2*cos(-pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 2 * cos(-pi/4) ** 2 - 1,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) - cos(pi/2) = - 2 * sin(-pi/2) * sin(0),
{
rw cos_sub_cos,
have : sin(((-pi/2) + (pi/2))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (pi/2))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end






lemma Trigo_1209_test (h0 : cos(-pi/2)≠ 0) (h1 : cos(-pi/6)≠ 0) (h2 : (1+tan(-pi/2)*tan(-pi/6))≠ 0) : sin(-pi/3) / cos(-pi/3)=(tan(-pi/2) - tan(-pi/6))/(1 + tan(-pi/2)*tan(-pi/6)):=
begin
have : tan(-pi/3) = ( tan(-pi/2) - tan(-pi/6) ) / ( 1 + tan(-pi/2) * tan(-pi/6) ),
{
have : tan(-pi/3) = tan((-pi/2) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end




lemma Trigo_1211_test : 2*sin(-pi/12)*cos(-pi/12)=sin(767*pi/6):=
begin
have : sin(-pi/6) = 2 * sin(-pi/12) * cos(-pi/12),
{
have : sin(-pi/6) = sin(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(767*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1212_test : (sin(2*pi)*sin(5*pi/2) + cos(2*pi)*cos(5*pi/2))*sin(pi)=sin(pi/2) / 2 + sin(3*pi/2) / 2:=
begin
have : sin(pi) * (sin(5 * pi / 2) * sin(2 * pi) + cos(5 * pi / 2) * cos(2 * pi)) = (sin(2*pi)*sin(5*pi/2) + cos(2*pi)*cos(5*pi/2))*sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(5*pi/2) * sin(2*pi) + cos(5*pi/2) * cos(2*pi),
{
have : cos(pi/2) = cos((5*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(pi/2) = sin(pi/2) / 2 + sin(3*pi/2) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (pi/2)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/2)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_1213_test : -sin(-pi)*sin(3*pi/2) + cos(-pi)*cos(3*pi/2)=- cos(55*pi/2):=
begin
have : -sin(3 * pi / 2) * sin(-pi) + cos(3 * pi / 2) * cos(-pi) = -sin(-pi)*sin(3*pi/2) + cos(-pi)*cos(3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(3*pi/2) * sin(-pi) + cos(3*pi/2) * cos(-pi),
{
have : cos(pi/2) = cos((3*pi/2) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(55*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1214_test : cos(337*pi/6)**2=cos(pi/3) / 2 + 1 / 2:=
begin
have : cos(pi/6) = cos(337*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) ** 2 = cos(pi/3) / 2 + 1 / 2,
{
have : cos(pi/3) = cos(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
end


lemma Trigo_1215_test : -3*cos(-pi/6) + cos(-2*pi) + 4*cos(-pi/6)**3=2 * cos(3*pi/4) * cos(-5*pi/4):=
begin
have : 4 * cos(-pi / 6) ** 3 - 3 * cos(-pi / 6) + cos((-2) * pi) = -3*cos(-pi/6) + cos(-2*pi) + 4*cos(-pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = 4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6),
{
have : cos(-pi/2) = cos(3*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) + cos(-2*pi) = 2 * cos(3*pi/4) * cos(-5*pi/4),
{
rw cos_add_cos,
have : cos(((-pi/2) + (-2*pi))/2) = cos(-5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (-2*pi))/2) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1216_test : sin(137*pi/2)=- cos(191*pi):=
begin
have : cos(2*pi) = sin(137*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - cos(191*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1217_test (h0 : sin(pi/3)≠ 0) (h1 : (2*sin(pi/3))≠ 0) : sin(2*pi/3)/(2*sin(pi/3))=cos(415*pi/3):=
begin
have : cos(pi/3) = sin(2*pi/3) / ( 2 * sin(pi/3) ),
{
have : sin(2*pi/3) = sin(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(415*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1218_test : -sin(79*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -sin(79*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3*pi/4) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_1219_test : cos(pi) + sin(125*pi/6)=2 * cos(-2*pi/3) * cos(pi/3):=
begin
have : sin(125 * pi / 6) + cos(pi) = cos(pi) + sin(125*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(125*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(pi) = 2 * cos(-2*pi/3) * cos(pi/3),
{
rw cos_add_cos,
have : cos(((-pi/3) + (pi))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (pi))/2) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_1220_test : sin(-pi/6) / cos(-pi/6)=-tan(265*pi/6):=
begin
have : tan(-pi/6) = -tan(265*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/6) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) / cos(-pi/6) = tan(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_1221_test : -1 + 2*cos(-5*pi/4)**2=sin(-pi/2) * sin(2*pi) + cos(-pi/2) * cos(2*pi):=
begin
have : 2 * cos((-5) * pi / 4) ** 2 - 1 = -1 + 2*cos(-5*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/2) = 2 * cos(-5*pi/4) ** 2 - 1,
{
have : cos(-5*pi/2) = cos(2*(-5*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/2) = sin(-pi/2) * sin(2*pi) + cos(-pi/2) * cos(2*pi),
{
have : cos(-5*pi/2) = cos((-pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw ← this,
end


lemma Trigo_1222_test : -cos(363*pi/2)=sin(126*pi):=
begin
have : sin(2*pi) = -cos(363*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(126*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end