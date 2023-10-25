import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_number_generalization_step2_0 : -sin(-8279*pi/9)=- sin(7381*pi/9):=
begin
have : -sin((-8279) * pi / 9) = -sin(-8279*pi/9),
{
field_simp at *,
},
have : cos(27331*pi/18) = sin(-8279*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (27331*pi/18) (299),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = -cos(27331*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/9) (759),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = - sin(7381*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/9) (410),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_1 : -32*sin(5*pi/36)**3*cos(5*pi/36)**3 + 6*sin(5*pi/36)*cos(5*pi/36)=1 / 2:=
begin
have : (-4) * (2 * sin(5 * pi / 36) * cos(5 * pi / 36)) ** 3 + 3 * (2 * sin(5 * pi / 36) * cos(5 * pi / 36)) = -32*sin(5*pi/36)**3*cos(5*pi/36)**3 + 6*sin(5*pi/36)*cos(5*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = 2 * sin(5*pi/36) * cos(5*pi/36),
{
have : sin(5*pi/18) = sin(2*(5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(5 * pi / 18) ** 3 + 3 * sin(5 * pi / 18) = -4*sin(5*pi/18)**3 + 3*sin(5*pi/18),
{
field_simp at *,
},
have : sin(5*pi/6) = -4 * sin(5*pi/18) ** 3 + 3 * sin(5*pi/18),
{
have : sin(5*pi/6) = sin(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_2 : cos(269*pi/2)=- sin(1620*pi):=
begin
have : - -cos(269 * pi / 2) = cos(269*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1031*pi) = -cos(269*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1031*pi) (582),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(1031*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (516),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(1620*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (809),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_3 (h0 : cos(pi/9)≠ 0) (h1 : (2*cos(pi/9))≠ 0) (h2 : (2*(-1+2*cos(pi/18)**2))≠ 0) (h3 : (2*(2*cos(pi/18)**2-1))≠ 0) : sin(2*pi/9)/(2*(-1 + 2*cos(pi/18)**2))=sin(16453*pi/9):=
begin
have : sin(2 * pi / 9) / (2 * (2 * cos(pi / 18) ** 2 - 1)) = sin(2*pi/9)/(2*(-1 + 2*cos(pi/18)**2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = 2 * cos(pi/18) ** 2 - 1,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(2*pi/9) / ( 2 * cos(pi/9) ),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
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
have : sin(pi/9) = sin(16453*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/9) (914),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_4 : 2*sin(5*pi/9)*cos(5*pi/9)=sin(pi/9)*cos(pi) + sin(10*pi/9)/2 + sin(8*pi/9)/2:=
begin
have : sin(10*pi/9) = 2 * sin(5*pi/9) * cos(5*pi/9),
{
have : sin(10*pi/9) = sin(2*(5*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 9) * cos(pi) + (sin(8 * pi / 9) / 2 + sin(10 * pi / 9) / 2) = sin(pi/9)*cos(pi) + sin(10*pi/9)/2 + sin(8*pi/9)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * cos(pi/9) = sin(8*pi/9) / 2 + sin(10*pi/9) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (pi/9)) = sin(10*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/9)) = sin(8*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (sin(pi) * cos(pi/9)) = sin(pi)*cos(pi/9),
{
ring,
},
have : sin(10*pi/9) = sin(pi/9) * cos(pi) + sin(pi) * cos(pi/9),
{
have : sin(10*pi/9) = sin((pi/9) + (pi)),
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


lemma Trigo_number_generalization_step2_5 : -cos(13384*pi/5)=sin(14127*pi/10):=
begin
have : sin(18293*pi/10) = cos(13384*pi/5),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (18293*pi/10) (423),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -sin(18293*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (914),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = sin(14127*pi/10),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/5) (706),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_6 (h0 : sin(5683*pi/3)≠ 0) (h1 : (4*sin(5683*pi/3)**2)≠ 0) (h2 : (2*sin(5683*pi/3))≠ 0) : sin(-pi/3) ** 2=-sin(11366*pi/3)**2/(4*sin(5683*pi/3)**2) + 1:=
begin
have : 1 - (sin(11366 * pi / 3) / (2 * sin(5683 * pi / 3))) ** 2 = -sin(11366*pi/3)**2/(4*sin(5683*pi/3)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5683*pi/3) = sin(11366*pi/3) / ( 2 * sin(5683*pi/3) ),
{
have : sin(11366*pi/3) = sin(2*(5683*pi/3)),
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
have : cos(-pi/3) = cos(5683*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (947),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) ** 2 = 1 - cos(-pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_7 : 4*cos(11657*pi/12)**3 - 3*cos(11657*pi/12)=sqrt( 2 ) / 2:=
begin
have : (-4) * (-cos(11657 * pi / 12)) ** 3 + 3 * -cos(11657 * pi / 12) = 4*cos(11657*pi/12)**3 - 3*cos(11657*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(11657*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (485),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 12) ** 3 + 3 * sin(pi / 12) = -4*sin(pi/12)**3 + 3*sin(pi/12),
{
field_simp at *,
},
have : sin(pi/4) = -4 * sin(pi/12) ** 3 + 3 * sin(pi/12),
{
have : sin(pi/4) = sin(3*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_8 (h0 : cos(8*pi/3)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (tan(2*pi)*tan(8*pi/3)+1)≠ 0) (h3 : (1+tan(8*pi/3)*tan(2*pi))≠ 0) (h4 : cos((16*pi/3)/2)≠ 0) (h5 : (tan(2*pi)*(sin(16*pi/3)/(1+cos(16*pi/3)))+1)≠ 0) (h6 : (cos(16*pi/3)+1)≠ 0) (h7 : (1+cos(16*pi/3))≠ 0) (h8 : (sin(16*pi/3)*tan(2*pi)/(cos(16*pi/3)+1)+1)≠ 0) : (sin(16*pi/3)/(cos(16*pi/3) + 1) - tan(2*pi))/(sin(16*pi/3)*tan(2*pi)/(cos(16*pi/3) + 1) + 1)=- sqrt( 3 ):=
begin
have : (sin(16 * pi / 3) / (1 + cos(16 * pi / 3)) - tan(2 * pi)) / (tan(2 * pi) * (sin(16 * pi / 3) / (1 + cos(16 * pi / 3))) + 1) = (sin(16*pi/3)/(cos(16*pi/3) + 1) - tan(2*pi))/(sin(16*pi/3)*tan(2*pi)/(cos(16*pi/3) + 1) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(8*pi/3) = sin(16*pi/3) / ( 1 + cos(16*pi/3) ),
{
have : tan(8*pi/3) = tan((16*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(8 * pi / 3) - tan(2 * pi)) / (1 + tan(8 * pi / 3) * tan(2 * pi)) = (tan(8*pi/3) - tan(2*pi))/(tan(2*pi)*tan(8*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = ( tan(8*pi/3) - tan(2*pi) ) / ( 1 + tan(8*pi/3) * tan(2*pi) ),
{
have : tan(2*pi/3) = tan((8*pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_9 : cos(-2*pi)*cos(11*pi/4) - sin(-2*pi)*sin(2907*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos((-2) * pi) * cos(11 * pi / 4) - sin((-2) * pi) * sin(2907 * pi / 4) = cos(-2*pi)*cos(11*pi/4) - sin(-2*pi)*sin(2907*pi/4),
{
field_simp at *,
},
have : sin(11*pi/4) = sin(2907*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (11*pi/4) (362),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(11 * pi / 4) * sin((-2) * pi) + cos(11 * pi / 4) * cos((-2) * pi) = cos(-2*pi)*cos(11*pi/4) - sin(-2*pi)*sin(11*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(11*pi/4) * sin(-2*pi) + cos(11*pi/4) * cos(-2*pi),
{
have : cos(3*pi/4) = cos((11*pi/4) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_10 (h0 : tan(1157*pi/2)≠ 0) (h1 : -tan(465*pi/2)≠ 0) (h2 : tan(465*pi/2)≠ 0) : -1/tan(465*pi/2)=0:=
begin
have : 1 / -tan(465 * pi / 2) = -1/tan(465*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1157*pi/2) = -tan(465*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (1157*pi/2) (811),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(1157*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (579),
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


lemma Trigo_number_generalization_step2_11 : sin(pi/4)*cos(4403*pi/3) + cos(pi/6)*cos(pi/4)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(4403 * pi / 3) * sin(pi / 4) + cos(pi / 6) * cos(pi / 4) = sin(pi/4)*cos(4403*pi/3) + cos(pi/6)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(4403*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (733),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 4) * sin(pi / 6) + cos(pi / 4) * cos(pi / 6) = sin(pi/6)*sin(pi/4) + cos(pi/6)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(pi/4) * sin(pi/6) + cos(pi/4) * cos(pi/6),
{
have : cos(pi/12) = cos((pi/4) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_12 : -1 + 2*cos(pi/8)**2=-sin(-3011*pi/4):=
begin
have : 2 * cos(pi / 8) ** 2 - 1 = -1 + 2*cos(pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = 2 * cos(pi/8) ** 2 - 1,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -sin((-3011) * pi / 4) = -sin(-3011*pi/4),
{
field_simp at *,
},
have : sin(4055*pi/4) = sin(-3011*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4055*pi/4) (130),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = - sin(4055*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (506),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_13 : -sin(531*pi)=(sin(-pi)*cos(3*pi/2) + sin(3*pi/2)*cos(-pi))*sin(2*pi) + cos(pi/2)*cos(2*pi):=
begin
have : cos(3*pi/2) = -sin(531*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/2) (264),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) * (sin(3 * pi / 2) * cos(-pi) + sin(-pi) * cos(3 * pi / 2)) + cos(2 * pi) * cos(pi / 2) = (sin(-pi)*cos(3*pi/2) + sin(3*pi/2)*cos(-pi))*sin(2*pi) + cos(pi/2)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(3*pi/2) * cos(-pi) + sin(-pi) * cos(3*pi/2),
{
have : sin(pi/2) = sin((3*pi/2) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_14 (h0 : cos(pi/18)≠ 0) (h1 : (1-tan(pi/18)**2)≠ 0) (h2 : cos(pi/36)≠ 0) (h3 : (1-tan(pi/36)**2)≠ 0) (h4 : ((1-tan(pi/36)**2)*(-4*tan(pi/36)**2/(1-tan(pi/36)**2)**2+1))≠ 0) (h5 : (1-(2*tan(pi/36)/(1-tan(pi/36)**2))**2)≠ 0) : 4*tan(pi/36)/((1 - tan(pi/36)**2)*(-4*tan(pi/36)**2/(1 - tan(pi/36)**2)**2 + 1))=1 / tan(5425*pi/18):=
begin
have : 2 * (2 * tan(pi / 36) / (1 - tan(pi / 36) ** 2)) / (1 - (2 * tan(pi / 36) / (1 - tan(pi / 36) ** 2)) ** 2) = 4*tan(pi/36)/((1 - tan(pi/36)**2)*(-4*tan(pi/36)**2/(1 - tan(pi/36)**2)**2 + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = 2 * tan(pi/36) / ( 1 - tan(pi/36) ** 2 ),
{
have : tan(pi/18) = tan(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 2 * tan(pi/18) / ( 1 - tan(pi/18) ** 2 ),
{
have : tan(pi/9) = tan(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 1 / tan(5425*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/9) (301),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_15 : sin(613*pi)=-cos(3253*pi/4)**2 + cos(-pi/4)**2:=
begin
have : cos(-pi/2) = sin(613*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (306),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = cos(3253*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (406),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(-pi/4) ** 2 + cos(-pi/4) ** 2,
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
rw this,
end


lemma Trigo_number_generalization_step2_16 : -cos(4368*pi/5)**2 + sin(4368*pi/5)**2=cos(1799*pi/5):=
begin
have : -(-sin(4368 * pi / 5) ** 2 + cos(4368 * pi / 5) ** 2) = -cos(4368*pi/5)**2 + sin(4368*pi/5)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(8736*pi/5) = -sin(4368*pi/5) ** 2 + cos(4368*pi/5) ** 2,
{
have : cos(8736*pi/5) = cos(2*(4368*pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -cos(8736*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/5) (873),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = cos(1799*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/5) (180),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_17 : 2*sin(2749*pi/8)*cos(2749*pi/8)=- sqrt( 2 ) / 2:=
begin
have : sin(2749*pi/4) = 2 * sin(2749*pi/8) * cos(2749*pi/8),
{
have : sin(2749*pi/4) = sin(2*(2749*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = sin(2749*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (343),
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


lemma Trigo_number_generalization_step2_18 : -sin(pi/6)**2 - cos(3075*pi/4) + cos(pi/6)**2=2 * cos(-7*pi/24) * cos(pi/24):=
begin
have : -sin(pi / 6) ** 2 + -cos(3075 * pi / 4) + cos(pi / 6) ** 2 = -sin(pi/6)**2 - cos(3075*pi/4) + cos(pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -cos(3075*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/4) (384),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi / 4) + (-sin(pi / 6) ** 2 + cos(pi / 6) ** 2) = -sin(pi/6)**2 + cos(-pi/4) + cos(pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(-pi/4) + cos(pi/3) = 2 * cos(-7*pi/24) * cos(pi/24),
{
rw cos_add_cos,
have : cos(((-pi/4) + (pi/3))/2) = cos(pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/4) - (pi/3))/2) = cos(-7*pi/24),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_19 (h0 : sin(pi/7)≠ 0) (h1 : (2*sin(pi/7))≠ 0) : sin(2*pi/7)*cos(-10*pi/21)/(2*sin(pi/7)) - sin(-10*pi/21)*sin(pi/7)=cos(2251*pi/3):=
begin
have : cos((-10) * pi / 21) * (sin(2 * pi / 7) / (2 * sin(pi / 7))) - sin((-10) * pi / 21) * sin(pi / 7) = sin(2*pi/7)*cos(-10*pi/21)/(2*sin(pi/7)) - sin(-10*pi/21)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = sin(2*pi/7) / ( 2 * sin(pi/7) ),
{
have : sin(2*pi/7) = sin(2*(pi/7)),
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
have : -sin((-10) * pi / 21) * sin(pi / 7) + cos((-10) * pi / 21) * cos(pi / 7) = cos(-10*pi/21)*cos(pi/7) - sin(-10*pi/21)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(-10*pi/21) * sin(pi/7) + cos(-10*pi/21) * cos(pi/7),
{
have : cos(-pi/3) = cos((-10*pi/21) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(2251*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (375),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_20 (h0 : cos(pi/6)≠ 0) (h1 : (1-tan(pi/6)**2)≠ 0) (h2 : cos((pi/3)/2)≠ 0) (h3 : sin(pi/3)≠ 0) (h4 : ((-(1-cos(pi/3))**2/sin(pi/3)**2+1)*sin(pi/3))≠ 0) (h5 : (1-((1-cos(pi/3))/sin(pi/3))**2)≠ 0) : 2*(1 - cos(pi/3))/((-(1 - cos(pi/3))**2/sin(pi/3)**2 + 1)*sin(pi/3))=sqrt( 3 ):=
begin
have : 2 * ((1 - cos(pi / 3)) / sin(pi / 3)) / (1 - ((1 - cos(pi / 3)) / sin(pi / 3)) ** 2) = 2*(1 - cos(pi/3))/((-(1 - cos(pi/3))**2/sin(pi/3)**2 + 1)*sin(pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/3) = 2 * tan(pi/6) / ( 1 - tan(pi/6) ** 2 ),
{
have : tan(pi/3) = tan(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_21 (h0 : cos(pi/12)≠ 0) : -cos(9185*pi/12)/cos(pi/12)=2 - sqrt( 3 ):=
begin
have : sin(pi/12) = -cos(9185*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (382),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = sin(pi/12) / cos(pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_22 : cos(-2*pi/3)=-cos(10333*pi/6)**2 + cos(-pi/3)**2:=
begin
have : -(-cos(10333 * pi / 6)) ** 2 + cos(-pi / 3) ** 2 = -cos(10333*pi/6)**2 + cos(-pi/3)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1079*pi/3) = -cos(10333*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1079*pi/3) (681),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = sin(1079*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (180),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) = - sin(-pi/3) ** 2 + cos(-pi/3) ** 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
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


lemma Trigo_number_generalization_step2_23 : sin(pi/9) ** 2=-cos(7*pi/72)*cos(pi/8)/2 + sin(7*pi/72)*sin(pi/8)/2 + 1/2:=
begin
have : 1 / 2 - (-sin(7 * pi / 72) * sin(pi / 8) + cos(7 * pi / 72) * cos(pi / 8)) / 2 = -cos(7*pi/72)*cos(pi/8)/2 + sin(7*pi/72)*sin(pi/8)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/9) = -sin(7*pi/72) * sin(pi/8) + cos(7*pi/72) * cos(pi/8),
{
have : cos(2*pi/9) = cos((7*pi/72) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - (cos(2 * pi / 9) / 2 + 1 / 2) = 1/2 - cos(2*pi/9)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) ** 2 = cos(2*pi/9) / 2 + 1 / 2,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/9) ** 2 = 1 - cos(pi/9) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_24 (h0 : cos(2*pi/45)≠ 0) (h1 : cos(2*pi/45)≠ 0) (h2 : (2*cos(2*pi/45))≠ 0) : cos(-pi/9) - cos(-pi/5)=-2*sin(-7*pi/90)*sin(4*pi/45)*cos(-7*pi/90)/cos(2*pi/45):=
begin
have : -(2 * sin((-7) * pi / 90) * cos((-7) * pi / 90)) * sin(4 * pi / 45) / cos(2 * pi / 45) = -2*sin(-7*pi/90)*sin(4*pi/45)*cos(-7*pi/90)/cos(2*pi/45),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-7*pi/45) = 2 * sin(-7*pi/90) * cos(-7*pi/90),
{
have : sin(-7*pi/45) = sin(2*(-7*pi/90)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : (-2) * (sin(4 * pi / 45) / (2 * cos(2 * pi / 45))) * sin((-7) * pi / 45) = -sin(-7*pi/45)*sin(4*pi/45)/cos(2*pi/45),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/45) = sin(4*pi/45) / ( 2 * cos(2*pi/45) ),
{
have : sin(4*pi/45) = sin(2*(2*pi/45)),
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
have : cos(-pi/9) - cos(-pi/5) = - 2 * sin(2*pi/45) * sin(-7*pi/45),
{
rw cos_sub_cos,
have : sin(((-pi/9) + (-pi/5))/2) = sin(-7*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/9) - (-pi/5))/2) = sin(2*pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_25 (h0 : tan(2213*pi/6)≠ 0) (h1 : cos((2213*pi/3)/2)≠ 0) (h2 : (1-cos(2213*pi/3))≠ 0) (h3 : ((1-cos(2213*pi/3))/sin(2213*pi/3))≠ 0) (h4 : sin(2213*pi/3)≠ 0) : sin(2213*pi/3)/(1 - cos(2213*pi/3))=- sqrt( 3 ):=
begin
have : 1 / ((1 - cos(2213 * pi / 3)) / sin(2213 * pi / 3)) = sin(2213*pi/3)/(1 - cos(2213*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2213*pi/6) = ( 1 - cos(2213*pi/3) ) / sin(2213*pi/3),
{
have : tan(2213*pi/6) = tan((2213*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = 1 / tan(2213*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (369),
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


lemma Trigo_number_generalization_step2_26 : sin(-pi/2) + (3*sin(-pi/15) - 4*sin(-pi/15)**3)*cos(13*pi/40) + sin(13*pi/40)*cos(-pi/5)=2 * sin(-3*pi/16) * cos(-5*pi/16):=
begin
have : sin(-pi / 2) + ((-4) * sin(-pi / 15) ** 3 + 3 * sin(-pi / 15)) * cos(13 * pi / 40) + sin(13 * pi / 40) * cos(-pi / 5) = sin(-pi/2) + (3*sin(-pi/15) - 4*sin(-pi/15)**3)*cos(13*pi/40) + sin(13*pi/40)*cos(-pi/5),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = -4 * sin(-pi/15) ** 3 + 3 * sin(-pi/15),
{
have : sin(-pi/5) = sin(3*(-pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) + (sin(13 * pi / 40) * cos(-pi / 5) + sin(-pi / 5) * cos(13 * pi / 40)) = sin(-pi/2) + sin(-pi/5)*cos(13*pi/40) + sin(13*pi/40)*cos(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = sin(13*pi/40) * cos(-pi/5) + sin(-pi/5) * cos(13*pi/40),
{
have : sin(pi/8) = sin((13*pi/40) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) + sin(pi/8) = 2 * sin(-3*pi/16) * cos(-5*pi/16),
{
rw sin_add_sin,
have : sin(((-pi/2) + (pi/8))/2) = sin(-3*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (pi/8))/2) = cos(-5*pi/16),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_27 (h0 : cos((4*pi/3)/2)≠ 0) (h1 : sin(4*pi/3)≠ 0) : (-cos(pi/8)*cos(35*pi/24) - sin(pi/8)*sin(35*pi/24) + 1)/sin(4*pi/3)=- sqrt( 3 ):=
begin
have : (1 - (sin(35 * pi / 24) * sin(pi / 8) + cos(35 * pi / 24) * cos(pi / 8))) / sin(4 * pi / 3) = (-cos(pi/8)*cos(35*pi/24) - sin(pi/8)*sin(35*pi/24) + 1)/sin(4*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/3) = sin(35*pi/24) * sin(pi/8) + cos(35*pi/24) * cos(pi/8),
{
have : cos(4*pi/3) = cos((35*pi/24) - (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = ( 1 - cos(4*pi/3) ) / sin(4*pi/3),
{
have : tan(2*pi/3) = tan((4*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_28 : -sin(-pi/8)**2 + (-sin(-pi/16)**2 + cos(-pi/16)**2)**2=- cos(3571*pi/4):=
begin
have : cos(-pi/8) = -sin(-pi/16) ** 2 + cos(-pi/16) ** 2,
{
have : cos(-pi/8) = cos(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -sin(-pi/8) ** 2 + cos(-pi/8) ** 2,
{
have : cos(-pi/4) = cos(2*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - cos(3571*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/4) (446),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_29 : -sin(pi/3)*cos(11609*pi/12) + cos(-pi/12)*cos(pi/3)=2 * cos(pi/8) ** 2 - 1:=
begin
have : -cos(11609 * pi / 12) * sin(pi / 3) + cos(-pi / 12) * cos(pi / 3) = -sin(pi/3)*cos(11609*pi/12) + cos(-pi/12)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = cos(11609*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/12) (483),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(-pi/12) * sin(pi/3) + cos(-pi/12) * cos(pi/3),
{
have : cos(pi/4) = cos((-pi/12) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = 2 * cos(pi/8) ** 2 - 1,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_30 : -sin(31705*pi/18)/2 - sin(31709*pi/18)/2=cos(-17*pi/9) / 2 + cos(19*pi/9) / 2:=
begin
have : -(sin(31705 * pi / 18) / 2 + sin(31709 * pi / 18) / 2) = -sin(31705*pi/18)/2 - sin(31709*pi/18)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3523*pi/2) * cos(pi/9) = sin(31705*pi/18) / 2 + sin(31709*pi/18) / 2,
{
rw sin_mul_cos,
have : sin((3523*pi/2) + (pi/9)) = sin(31709*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : sin((3523*pi/2) - (pi/9)) = sin(31705*pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(3523*pi/2) * cos(pi/9)) = -sin(3523*pi/2)*cos(pi/9),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi / 9) * -sin(3523 * pi / 2) = -sin(3523*pi/2)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(3523*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (881),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) * cos(2*pi) = cos(-17*pi/9) / 2 + cos(19*pi/9) / 2,
{
rw cos_mul_cos,
have : cos((pi/9) + (2*pi)) = cos(19*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (2*pi)) = cos(-17*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_31 : -sin(1039*pi)=0:=
begin
have : sin(849*pi) = -sin(1039*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (849*pi) (944),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(849*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (424),
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


lemma Trigo_number_generalization_step2_32 : sin(4853*pi/6)=1 / 2:=
begin
have : - -sin(4853 * pi / 6) = sin(4853*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(488*pi/3) = -sin(4853*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (488*pi/3) (485),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(488*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (81),
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


lemma Trigo_number_generalization_step2_33 : -sin(-pi/7)**2 + cos(-pi/7)**2=-1 + 2*cos(-pi/7)**2:=
begin
have : cos(-2*pi/7) = -sin(-pi/7) ** 2 + cos(-pi/7) ** 2,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - cos(-pi / 7) ** 2) + cos(-pi / 7) ** 2 = -1 + 2*cos(-pi/7)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) ** 2 = 1 - cos(-pi/7) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/7) = - sin(-pi/7) ** 2 + cos(-pi/7) ** 2,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
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


lemma Trigo_number_generalization_step2_34 (h0 : cos(pi/7)≠ 0) (h1 : (2*cos(pi/7))≠ 0) : sin(2*pi/7)/(2*cos(pi/7))=-sin(-8821*pi/7):=
begin
have : sin(pi/7) = sin(2*pi/7) / ( 2 * cos(pi/7) ),
{
have : sin(2*pi/7) = sin(2*(pi/7)),
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
have : -sin((-8821) * pi / 7) = -sin(-8821*pi/7),
{
field_simp at *,
},
have : cos(19651*pi/14) = -sin(-8821*pi/7),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (19651*pi/14) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = cos(19651*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (701),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_35 : sin(-pi/5) * sin(pi/9)=sin(60083*pi/90)/2 - sin(39223*pi/90)/2:=
begin
have : sin(60083 * pi / 90) / 2 + -sin(39223 * pi / 90) / 2 = sin(60083*pi/90)/2 - sin(39223*pi/90)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-14*pi/45) = -sin(39223*pi/90),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-14*pi/45) (217),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos((-14) * pi / 45) / 2 - -sin(60083 * pi / 90) / 2 = sin(60083*pi/90)/2 + cos(-14*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi/45) = -sin(60083*pi/90),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-4*pi/45) (333),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/5) * sin(pi/9) = cos(-14*pi/45) / 2 - cos(-4*pi/45) / 2,
{
rw sin_mul_sin,
have : cos((-pi/5) + (pi/9)) = cos(-4*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (pi/9)) = cos(-14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_36 : sin(8745*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -sin(8745 * pi / 4) = sin(8745*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2635*pi/4) = -sin(8745*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2635*pi/4) (763),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(2635*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (329),
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


lemma Trigo_number_generalization_step2_37 : (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))**2=1/2 - sin(2577*pi/2)/2:=
begin
have : cos(4*pi) = sin(2577*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi) (646),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) ** 2 = (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))**2,
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
have : sin(2*pi) ** 2 = 1 / 2 - cos(4*pi) / 2,
{
have : cos(4*pi) = cos(2*(2*pi)),
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


lemma Trigo_number_generalization_step2_38 : -1 + 2*cos(3909*pi/2)**2=- cos(1366*pi):=
begin
have : -1 + 2 * (-cos(3909 * pi / 2)) ** 2 = -1 + 2*cos(3909*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -cos(3909*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (977),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(-pi / 2) ** 2 - 1 = -1 + 2*cos(-pi/2)**2,
{
field_simp at *,
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
have : cos(-pi) = - cos(1366*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (682),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_39 (h0 : cos(2136*pi/5)≠ 0) (h1 : -cos(2136*pi/5)≠ 0) (h2 : cos(-pi/5)≠ 0) (h3 : (2*cos(-pi/5))≠ 0) (h4 : (2*cos(-pi/5)*cos(2136*pi/5))≠ 0) : -sin(-2*pi/5)/(2*cos(-pi/5)*cos(2136*pi/5))=tan(-pi/5):=
begin
have : -(sin((-2) * pi / 5) / (2 * cos(-pi / 5))) / cos(2136 * pi / 5) = -sin(-2*pi/5)/(2*cos(-pi/5)*cos(2136*pi/5)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = sin(-2*pi/5) / ( 2 * cos(-pi/5) ),
{
have : sin(-2*pi/5) = sin(2*(-pi/5)),
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
have : sin(-pi / 5) / -cos(2136 * pi / 5) = -sin(-pi/5)/cos(2136*pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = -cos(2136*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/5) (213),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) / cos(-pi/5) = tan(-pi/5),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_40 : -sin(-2*pi)*sin(13*pi/6) + (1 - 2*sin(-pi)**2)*cos(13*pi/6)=sqrt( 3 ) / 2:=
begin
have : -sin((-2) * pi) * sin(13 * pi / 6) + (1 - 2 * sin(-pi) ** 2) * cos(13 * pi / 6) = -sin(-2*pi)*sin(13*pi/6) + (1 - 2*sin(-pi)**2)*cos(13*pi/6),
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
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_41 : sin(57511*pi/90)*cos(pi/9) - sin(pi/9)*cos(57511*pi/90)=1 - 2 * sin(-pi/5) ** 2:=
begin
have : sin(6389*pi/10) = sin(57511*pi/90) * cos(pi/9) - sin(pi/9) * cos(57511*pi/90),
{
have : sin(6389*pi/10) = sin((57511*pi/90) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = sin(6389*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi/5) (319),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = 1 - 2 * sin(-pi/5) ** 2,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_42 : -3*sin(313*pi/9) + 4*sin(313*pi/9)**3=- sqrt( 3 ) / 2:=
begin
have : (-3) * sin(313 * pi / 9) + 4 * sin(313 * pi / 9) ** 3 = -3*sin(313*pi/9) + 4*sin(313*pi/9)**3,
{
field_simp at *,
},
have : cos(5*pi/18) = sin(313*pi/9),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(5 * pi / 18) ** 3 - 3 * cos(5 * pi / 18) = -3*cos(5*pi/18) + 4*cos(5*pi/18)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = 4 * cos(5*pi/18) ** 3 - 3 * cos(5*pi/18),
{
have : cos(5*pi/6) = cos(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_43 : -1 + 2*cos(pi/5)**2=-8*sin(pi/10)**2*cos(pi/10)**2 + 1:=
begin
have : 2 * cos(pi / 5) ** 2 - 1 = -1 + 2*cos(pi/5)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/5) = 2 * cos(pi/5) ** 2 - 1,
{
have : cos(2*pi/5) = cos(2*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (2 * sin(pi / 10) * cos(pi / 10)) ** 2 = -8*sin(pi/10)**2*cos(pi/10)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/5) = 2 * sin(pi/10) * cos(pi/10),
{
have : sin(pi/5) = sin(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/5) = 1 - 2 * sin(pi/5) ** 2,
{
have : cos(2*pi/5) = cos(2*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_44 : -1 + 2*sin(1477*pi/4)**2=0:=
begin
have : -(1 - 2 * sin(1477 * pi / 4) ** 2) = -1 + 2*sin(1477*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1477*pi/2) = 1 - 2 * sin(1477*pi/4) ** 2,
{
have : cos(1477*pi/2) = cos(2*(1477*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(1477*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (369),
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


lemma Trigo_number_generalization_step2_45 : -1 - cos(pi/9) + 2*cos(pi/16)**2=2*sin(pi/144)*sin(57761*pi/144):=
begin
have : (-2) * sin(pi / 144) * -sin(57761 * pi / 144) = 2*sin(pi/144)*sin(57761*pi/144),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(17*pi/144) = -sin(57761*pi/144),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (17*pi/144) (200),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * cos(pi / 16) ** 2 - 1 - cos(pi / 9) = -1 - cos(pi/9) + 2*cos(pi/16)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = 2 * cos(pi/16) ** 2 - 1,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) - cos(pi/9) = - 2 * sin(pi/144) * sin(17*pi/144),
{
rw cos_sub_cos,
have : sin(((pi/8) + (pi/9))/2) = sin(17*pi/144),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/8) - (pi/9))/2) = sin(pi/144),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_46 : cos(5181*pi/7)=- cos(4108*pi/7):=
begin
have : sin(5801*pi/14) = cos(5181*pi/7),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5801*pi/14) (577),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = sin(5801*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/7) (207),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = - cos(4108*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/7) (293),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_47 : sin(4*pi/3)*cos(pi/3) - sin(4550*pi/3)*cos(4*pi/3)=0:=
begin
have : sin(pi/3) = sin(4550*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (758),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_48 (h0 : cos(4990*pi/9)≠ 0) (h1 : cos(pi/9)≠ 0) (h2 : (1+tan(4990*pi/9)*tan(pi/9))≠ 0) (h3 : (1+tan(pi/9)*tan(4990*pi/9))≠ 0) : -(-tan(pi/9) + tan(4990*pi/9))/(1 + tan(pi/9)*tan(4990*pi/9))=- sqrt( 3 ):=
begin
have : -((tan(4990 * pi / 9) - tan(pi / 9)) / (1 + tan(4990 * pi / 9) * tan(pi / 9))) = -(-tan(pi/9) + tan(4990*pi/9))/(1 + tan(pi/9)*tan(4990*pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(1663*pi/3) = ( tan(4990*pi/9) - tan(pi/9) ) / ( 1 + tan(4990*pi/9) * tan(pi/9) ),
{
have : tan(1663*pi/3) = tan((4990*pi/9) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(1663*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (555),
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


lemma Trigo_number_generalization_step2_49 (h0 : (2*cos(pi)**2-1)≠ 0) (h1 : (-1+2*cos(pi)**2)≠ 0) : sin(2*pi)/(-1 + 2*cos(pi)**2)=-tan(709*pi):=
begin
have : tan(2*pi) = -tan(709*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (711),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2 * pi) / (2 * cos(pi) ** 2 - 1) = sin(2*pi)/(-1 + 2*cos(pi)**2),
{
field_simp at *,
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
have : sin(2*pi) / cos(2*pi) = tan(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_50 : sin(795*pi/2)=sin(1119*pi/2):=
begin
have : cos(31*pi) = sin(795*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (31*pi) (214),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(31*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(1119*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (280),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_51 : -sin(3326*pi/3)*cos(-pi/6) - sin(-17*pi/6)*sin(-pi/6)=4 * cos(-pi) ** 3 - 3 * cos(-pi):=
begin
have : -sin(3326 * pi / 3) * cos(-pi / 6) - sin((-17) * pi / 6) * sin(-pi / 6) = -sin(3326*pi/3)*cos(-pi/6) - sin(-17*pi/6)*sin(-pi/6),
{
field_simp at *,
},
have : cos(-17*pi/6) = -sin(3326*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-17*pi/6) (555),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-17) * pi / 6) * sin(-pi / 6) + cos((-17) * pi / 6) * cos(-pi / 6) = cos(-17*pi/6)*cos(-pi/6) - sin(-17*pi/6)*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi) = -sin(-17*pi/6) * sin(-pi/6) + cos(-17*pi/6) * cos(-pi/6),
{
have : cos(-3*pi) = cos((-17*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi) = 4 * cos(-pi) ** 3 - 3 * cos(-pi),
{
have : cos(-3*pi) = cos(3*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_52 : -cos(pi/9)*cos(6266*pi/5)=cos(4*pi/45) / 2 + cos(14*pi/45) / 2:=
begin
have : cos(1306*pi/5) = cos(6266*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (1306*pi/5) (496),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(1306 * pi / 5) * cos(pi / 9) = -cos(pi/9)*cos(1306*pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -cos(1306*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/5) (130),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) * cos(pi/9) = cos(4*pi/45) / 2 + cos(14*pi/45) / 2,
{
rw cos_mul_cos,
have : cos((pi/5) + (pi/9)) = cos(14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/5) - (pi/9)) = cos(4*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_53 : -cos(7701*pi/4)=1 - 2*cos(1203*pi/8)**2:=
begin
have : cos(pi/4) = -cos(7701*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (962),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = cos(1203*pi/8),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/8) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = 1 - 2 * sin(pi/8) ** 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_54 : sin(pi)=-cos(2421*pi/2):=
begin
have : cos(1135*pi/2) = cos(2421*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (1135*pi/2) (889),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(573*pi/2) = cos(1135*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (573*pi/2) (427),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = - cos(573*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (143),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_55 : -sin(963*pi)*cos(-4*pi) + sin(-4*pi)*cos(-2*pi)=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : -sin(963 * pi) * cos((-4) * pi) + sin((-4) * pi) * cos((-2) * pi) = -sin(963*pi)*cos(-4*pi) + sin(-4*pi)*cos(-2*pi),
{
field_simp at *,
},
have : sin(-2*pi) = -sin(963*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (482),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-4) * pi) * cos((-2) * pi) + sin((-2) * pi) * cos((-4) * pi) = sin(-2*pi)*cos(-4*pi) + sin(-4*pi)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-6*pi) = sin(-4*pi) * cos(-2*pi) + sin(-2*pi) * cos(-4*pi),
{
have : sin(-6*pi) = sin((-4*pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step2_56 : -2*(-sin(pi/20)**2 + cos(pi/20)**2)**2 + cos(pi/2) + 1=- 2 * sin(3*pi/20) * sin(7*pi/20):=
begin
have : (-2) * (-sin(pi / 20) ** 2 + cos(pi / 20) ** 2) ** 2 + cos(pi / 2) + 1 = -2*(-sin(pi/20)**2 + cos(pi/20)**2)**2 + cos(pi/2) + 1,
{
field_simp at *,
},
have : cos(pi/10) = -sin(pi/20) ** 2 + cos(pi/20) ** 2,
{
have : cos(pi/10) = cos(2*(pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 2) - (2 * cos(pi / 10) ** 2 - 1) = -2*cos(pi/10)**2 + cos(pi/2) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = 2 * cos(pi/10) ** 2 - 1,
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) - cos(pi/5) = - 2 * sin(3*pi/20) * sin(7*pi/20),
{
rw cos_sub_cos,
have : sin(((pi/2) + (pi/5))/2) = sin(7*pi/20),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (pi/5))/2) = sin(3*pi/20),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_57 : 4*cos(949*pi/4)**3 - 3*cos(949*pi/4)=sqrt( 2 ) / 2:=
begin
have : (-4) * (-cos(949 * pi / 4)) ** 3 + 3 * -cos(949 * pi / 4) = 4*cos(949*pi/4)**3 - 3*cos(949*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(949*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (118),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 4) ** 3 + 3 * sin(pi / 4) = -4*sin(pi/4)**3 + 3*sin(pi/4),
{
field_simp at *,
},
have : sin(3*pi/4) = -4 * sin(pi/4) ** 3 + 3 * sin(pi/4),
{
have : sin(3*pi/4) = sin(3*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_58 : -cos(pi/5)*cos(28699*pi/30) + sin(pi/5)*sin(28699*pi/30)=sqrt( 3 ) / 2:=
begin
have : -(-sin(28699 * pi / 30) * sin(pi / 5) + cos(28699 * pi / 30) * cos(pi / 5)) = -cos(pi/5)*cos(28699*pi/30) + sin(pi/5)*sin(28699*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5741*pi/6) = -sin(28699*pi/30) * sin(pi/5) + cos(28699*pi/30) * cos(pi/5),
{
have : cos(5741*pi/6) = cos((28699*pi/30) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(5741*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (478),
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


lemma Trigo_number_generalization_step2_59 : cos(2*pi/7)=-1 + cos(pi/7)**2 + cos(12601*pi/7)**2:=
begin
have : -(1 - cos(12601 * pi / 7) ** 2) + cos(pi / 7) ** 2 = -1 + cos(pi/7)**2 + cos(12601*pi/7)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(12601*pi/7) ** 2 = 1 - cos(12601*pi/7) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = sin(12601*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/7) (900),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/7) = - sin(pi/7) ** 2 + cos(pi/7) ** 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
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


lemma Trigo_number_generalization_step2_60 : cos(50869*pi/30)=-sin(pi/6)*cos(15623*pi/10) + cos(pi/6)*cos(pi/5):=
begin
have : sin(pi/5) = cos(15623*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (781),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(11*pi/30) = cos(50869*pi/30),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (11*pi/30) (848),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/30) = - sin(pi/6) * sin(pi/5) + cos(pi/6) * cos(pi/5),
{
have : cos(11*pi/30) = cos((pi/6) + (pi/5)),
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


lemma Trigo_number_generalization_step2_61 (h0 : sin(pi/5)≠ 0) (h1 : (2*sin(pi/5))≠ 0) : sin(2*pi/5)/(2*sin(pi/5))=sin(29192*pi/15)*cos(pi/6) + sin(pi/6)*cos(29192*pi/15):=
begin
have : cos(pi/5) = sin(2*pi/5) / ( 2 * sin(pi/5) ),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
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
have : sin(19463*pi/10) = sin(29192*pi/15) * cos(pi/6) + sin(pi/6) * cos(29192*pi/15),
{
have : sin(19463*pi/10) = sin((29192*pi/15) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = sin(19463*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (973),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_62 : cos(pi/3)*cos(2061*pi/8)=sin(47837*pi/24)/2 + sin(11*pi/24)/2:=
begin
have : sin(-5*pi/24) = sin(47837*pi/24),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-5*pi/24) (996),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2061 * pi / 8) * cos(pi / 3) = cos(pi/3)*cos(2061*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = cos(2061*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (128),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) * cos(pi/3) = sin(-5*pi/24) / 2 + sin(11*pi/24) / 2,
{
rw sin_mul_cos,
have : sin((pi/8) + (pi/3)) = sin(11*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (pi/3)) = sin(-5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_63 : sin(13*pi/40)=sin(pi/8)*cos(-pi/5) - (-sin(pi/16)**2 + cos(pi/8)/2 + 1/2)*sin(-pi/5):=
begin
have : sin(pi / 8) * cos(-pi / 5) - (-sin(pi / 16) ** 2 + (cos(pi / 8) / 2 + 1 / 2)) * sin(-pi / 5) = sin(pi/8)*cos(-pi/5) - (-sin(pi/16)**2 + cos(pi/8)/2 + 1/2)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/16) ** 2 = cos(pi/8) / 2 + 1 / 2,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 8) * cos(-pi / 5) - sin(-pi / 5) * (-sin(pi / 16) ** 2 + cos(pi / 16) ** 2) = sin(pi/8)*cos(-pi/5) - (-sin(pi/16)**2 + cos(pi/16)**2)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = -sin(pi/16) ** 2 + cos(pi/16) ** 2,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(13*pi/40) = sin(pi/8) * cos(-pi/5) - sin(-pi/5) * cos(pi/8),
{
have : sin(13*pi/40) = sin((pi/8) - (-pi/5)),
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


lemma Trigo_number_generalization_step2_64 (h0 : cos(2*pi/3)≠ 0) : cos(11147*pi/6)/cos(2*pi/3)=- sqrt( 3 ):=
begin
have : sin(2*pi/3) = cos(11147*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (929),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = sin(2*pi/3) / cos(2*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_65 (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : sin(-pi/8) + cos(7273*pi/6)/(2*cos(pi/3))=2 * sin(5*pi/48) * cos(11*pi/48):=
begin
have : sin(2*pi/3) = cos(7273*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (605),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi / 3) / (2 * cos(pi / 3)) + sin(-pi / 8) = sin(-pi/8) + sin(2*pi/3)/(2*cos(pi/3)),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi/3) + sin(-pi/8) = 2 * sin(5*pi/48) * cos(11*pi/48),
{
rw sin_add_sin,
have : sin(((pi/3) + (-pi/8))/2) = sin(5*pi/48),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (-pi/8))/2) = cos(11*pi/48),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_66 : 1 - 2*sin(-pi/4)**2=-cos(-453*pi/2):=
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
have : -cos((-453) * pi / 2) = -cos(-453*pi/2),
{
field_simp at *,
},
have : sin(884*pi) = -cos(-453*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (884*pi) (328),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(884*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (442),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_67 : sin(2*pi) * sin(-pi/3)=-cos(5233*pi/3)/2 + sin(4333*pi/6)/2:=
begin
have : cos(7*pi/3) = sin(4333*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/3) (362),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7 * pi / 3) / 2 - cos(5233 * pi / 3) / 2 = -cos(5233*pi/3)/2 + cos(7*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/3) = cos(5233*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/3) (873),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * sin(-pi/3) = cos(7*pi/3) / 2 - cos(5*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((2*pi) + (-pi/3)) = cos(5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (-pi/3)) = cos(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_68 (h0 : tan(3257*pi/4)≠ 0) (h1 : tan(5637*pi/4)≠ 0) : 1/tan(5637*pi/4)=1:=
begin
have : tan(3257*pi/4) = tan(5637*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (3257*pi/4) (595),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1 / tan(3257*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (814),
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


lemma Trigo_number_generalization_step2_69 (h0 : cos(pi/8)≠ 0) (h1 : (1-tan(pi/8)**2)≠ 0) (h2 : ((1-1/tan(667*pi/8)**2)*tan(667*pi/8))≠ 0) (h3 : tan(667*pi/8)≠ 0) (h4 : (1-(1/tan(667*pi/8))**2)≠ 0) : 2/((1 - 1/tan(667*pi/8)**2)*tan(667*pi/8))=1:=
begin
have : 2 * (1 / tan(667 * pi / 8)) / (1 - (1 / tan(667 * pi / 8)) ** 2) = 2/((1 - 1/tan(667*pi/8)**2)*tan(667*pi/8)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = 1 / tan(667*pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/8) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 2 * tan(pi/8) / ( 1 - tan(pi/8) ** 2 ),
{
have : tan(pi/4) = tan(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_70 : cos(3827*pi/3)=-sin(5998*pi/3)*cos(-pi/2) + sin(-pi/2)*cos(5998*pi/3):=
begin
have : -(sin(5998 * pi / 3) * cos(-pi / 2) - sin(-pi / 2) * cos(5998 * pi / 3)) = -sin(5998*pi/3)*cos(-pi/2) + sin(-pi/2)*cos(5998*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(11999*pi/6) = sin(5998*pi/3) * cos(-pi/2) - sin(-pi/2) * cos(5998*pi/3),
{
have : sin(11999*pi/6) = sin((5998*pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = cos(3827*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (637),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(11999*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (1000),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_71 : sin(1961*pi/3)=- 4 * sin(-pi/9) ** 3 + 3 * sin(-pi/9):=
begin
have : - -sin(1961 * pi / 3) = sin(1961*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(6971*pi/6) = -sin(1961*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (6971*pi/6) (907),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -cos(6971*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (580),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - 4 * sin(-pi/9) ** 3 + 3 * sin(-pi/9),
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
rw this,
end


lemma Trigo_number_generalization_step2_72 (h0 : sin(-pi/7)≠ 0) (h1 : (2*sin(-pi/7))≠ 0) : (3*sin(-2*pi/21) - 4*sin(-2*pi/21)**3)*cos(pi/6)/(2*sin(-pi/7))=cos(13*pi/42) / 2 + cos(pi/42) / 2:=
begin
have : ((-4) * sin((-2) * pi / 21) ** 3 + 3 * sin((-2) * pi / 21)) * cos(pi / 6) / (2 * sin(-pi / 7)) = (3*sin(-2*pi/21) - 4*sin(-2*pi/21)**3)*cos(pi/6)/(2*sin(-pi/7)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/7) = -4 * sin(-2*pi/21) ** 3 + 3 * sin(-2*pi/21),
{
have : sin(-2*pi/7) = sin(3*(-2*pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 6) * (sin((-2) * pi / 7) / (2 * sin(-pi / 7))) = sin(-2*pi/7)*cos(pi/6)/(2*sin(-pi/7)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = sin(-2*pi/7) / ( 2 * sin(-pi/7) ),
{
have : sin(-2*pi/7) = sin(2*(-pi/7)),
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
have : cos(pi/6) * cos(-pi/7) = cos(13*pi/42) / 2 + cos(pi/42) / 2,
{
rw cos_mul_cos,
have : cos((pi/6) + (-pi/7)) = cos(pi/42),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (-pi/7)) = cos(13*pi/42),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_73 : (-1 + 2*cos(pi/16)**2)*cos(3823*pi/7)=cos(pi/56) / 2 + cos(15*pi/56) / 2:=
begin
have : cos(pi/7) = cos(3823*pi/7),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/7) (273),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 7) * (2 * cos(pi / 16) ** 2 - 1) = (-1 + 2*cos(pi/16)**2)*cos(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = 2 * cos(pi/16) ** 2 - 1,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) * cos(pi/8) = cos(pi/56) / 2 + cos(15*pi/56) / 2,
{
rw cos_mul_cos,
have : cos((pi/7) + (pi/8)) = cos(15*pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/7) - (pi/8)) = cos(pi/56),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_74 : 1 - 2*cos(3811*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : -(2 * cos(3811 * pi / 12) ** 2 - 1) = 1 - 2*cos(3811*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3811*pi/6) = 2 * cos(3811*pi/12) ** 2 - 1,
{
have : cos(3811*pi/6) = cos(2*(3811*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(3811*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (317),
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


lemma Trigo_number_generalization_step2_75 : -1 + 2*cos(6137*pi/6)**2=1 / 2:=
begin
have : -1 + 2 * (-cos(6137 * pi / 6)) ** 2 = -1 + 2*cos(6137*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(6137*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (511),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 6) ** 2 - 1 = -1 + 2*cos(pi/6)**2,
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_76 (h0 : sin(-9*pi/14)≠ 0) (h1 : (2*sin((-9)*pi/14))≠ 0) (h2 : (2*sin(-9*pi/14))≠ 0) : sin(-9*pi/14)*cos(-pi/7) - sin(-9*pi/7)*sin(-pi/7)/(2*sin(-9*pi/14))=- cos(1122*pi):=
begin
have : sin((-9) * pi / 14) * cos(-pi / 7) - sin(-pi / 7) * (sin((-9) * pi / 7) / (2 * sin((-9) * pi / 14))) = sin(-9*pi/14)*cos(-pi/7) - sin(-9*pi/7)*sin(-pi/7)/(2*sin(-9*pi/14)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-9*pi/14) = sin(-9*pi/7) / ( 2 * sin(-9*pi/14) ),
{
have : sin(-9*pi/7) = sin(2*(-9*pi/14)),
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
have : sin((-9) * pi / 14) * cos(-pi / 7) - sin(-pi / 7) * cos((-9) * pi / 14) = sin(-9*pi/14)*cos(-pi/7) - sin(-pi/7)*cos(-9*pi/14),
{
field_simp at *,
},
have : sin(-pi/2) = sin(-9*pi/14) * cos(-pi/7) - sin(-pi/7) * cos(-9*pi/14),
{
have : sin(-pi/2) = sin((-9*pi/14) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - cos(1122*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (561),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_77 : -cos(61*pi/2)=1 - 2*cos(4643*pi/4)**2:=
begin
have : 1 - 2 * (-cos(4643 * pi / 4)) ** 2 = 1 - 2*cos(4643*pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) = -cos(4643*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (580),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -cos(61*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step2_78 : cos(1223*pi/2)**2=1 - (1 - 2*sin(pi)**2)**2:=
begin
have : sin(2*pi) = cos(1223*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (304),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 1 - 2 * sin(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) ** 2 = 1 - cos(2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_79 (h0 : cos(pi/3)≠ 0) (h1 : (1-tan(pi/3)**2)≠ 0) (h2 : cos((2*pi/3)/2)≠ 0) (h3 : (1-(sin(2*pi/3)/(1+cos(2*pi/3)))**2)≠ 0) (h4 : (cos(2*pi/3)+1)≠ 0) (h5 : (1+cos(2*pi/3))≠ 0) (h6 : ((-sin(2*pi/3)**2/(cos(2*pi/3)+1)**2+1)*(cos(2*pi/3)+1))≠ 0) : 2*sin(2*pi/3)/((-sin(2*pi/3)**2/(cos(2*pi/3) + 1)**2 + 1)*(cos(2*pi/3) + 1))=- sqrt( 3 ):=
begin
have : 2 * (sin(2 * pi / 3) / (1 + cos(2 * pi / 3))) / (1 - (sin(2 * pi / 3) / (1 + cos(2 * pi / 3))) ** 2) = 2*sin(2*pi/3)/((-sin(2*pi/3)**2/(cos(2*pi/3) + 1)**2 + 1)*(cos(2*pi/3) + 1)),
{
field_simp at *,
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
have : tan(2*pi/3) = 2 * tan(pi/3) / ( 1 - tan(pi/3) ** 2 ),
{
have : tan(2*pi/3) = tan(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_80 : 1 - 2*cos(1165*pi/4)**2=0:=
begin
have : -(2 * cos(1165 * pi / 4) ** 2 - 1) = 1 - 2*cos(1165*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1165*pi/2) = 2 * cos(1165*pi/4) ** 2 - 1,
{
have : cos(1165*pi/2) = cos(2*(1165*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(1165*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (291),
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


lemma Trigo_number_generalization_step2_81 : -cos(1791*pi/2)=0:=
begin
have : sin(508*pi) = cos(1791*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (508*pi) (193),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(508*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (253),
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


lemma Trigo_number_generalization_step2_82 (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : -sin(pi)*cos(952*pi)/(2*cos(pi/2))=- sin(pi/2) / 2 + sin(3*pi/2) / 2:=
begin
have : -(sin(pi) / (2 * cos(pi / 2))) * cos(952 * pi) = -sin(pi)*cos(952*pi)/(2*cos(pi/2)),
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
have : sin(pi / 2) * -cos(952 * pi) = -sin(pi/2)*cos(952*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(952*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (476),
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


lemma Trigo_number_generalization_step2_83 : cos(-1499*pi)=- 1:=
begin
have : - -cos((-1499) * pi) = cos(-1499*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3237*pi/2) = -cos(-1499*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3237*pi/2) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(3237*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (808),
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


lemma Trigo_number_generalization_step2_84 (h0 : cos(3851*pi/12)≠ 0) : -sin(3851*pi/12)/cos(3851*pi/12)=2 - sqrt( 3 ):=
begin
have : -(sin(3851 * pi / 12) / cos(3851 * pi / 12)) = -sin(3851*pi/12)/cos(3851*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3851*pi/12) = sin(3851*pi/12) / cos(3851*pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(3851*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (321),
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


lemma Trigo_number_generalization_step2_85 (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) : tan(-2*pi)=sin(-349*pi)/cos(-2*pi):=
begin
have : - -sin((-349) * pi) / cos((-2) * pi) = sin(-349*pi)/cos(-2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(913*pi) = -sin(-349*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (913*pi) (282),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -sin(913 * pi) / cos((-2) * pi) = -sin(913*pi)/cos(-2*pi),
{
field_simp at *,
},
have : sin(-2*pi) = -sin(913*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (457),
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


lemma Trigo_number_generalization_step2_86 : sin(7235*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -sin(7235 * pi / 4) = sin(7235*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1037*pi/4) = -sin(7235*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (1037*pi/4) (774),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = -cos(1037*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (129),
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


lemma Trigo_number_generalization_step2_87 : 1 - 2*cos(805*pi)**2=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : sin(3*pi/2) = cos(805*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/2) (403),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = 1 - 2 * sin(3*pi/2) ** 2,
{
have : cos(3*pi) = cos(2*(3*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = 4 * cos(pi) ** 3 - 3 * cos(pi),
{
have : cos(3*pi) = cos(3*(pi)),
{
apply congr_arg,
ring,
},
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_88 : -sin(330*pi)*cos(pi/6) + sin(pi/6)*cos(330*pi)=1 / 2:=
begin
have : -(sin(330 * pi) * cos(pi / 6) - sin(pi / 6) * cos(330 * pi)) = -sin(330*pi)*cos(pi/6) + sin(pi/6)*cos(330*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1979*pi/6) = sin(330*pi) * cos(pi/6) - sin(pi/6) * cos(330*pi),
{
have : sin(1979*pi/6) = sin((330*pi) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(1979*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (165),
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


lemma Trigo_number_generalization_step2_89 : -cos(-5*pi/6)*cos(2195*pi/2) + sin(-5*pi/6)*cos(-pi)=sin(6889*pi/6):=
begin
have : -cos(2195 * pi / 2) * cos((-5) * pi / 6) + sin((-5) * pi / 6) * cos(-pi) = -cos(-5*pi/6)*cos(2195*pi/2) + sin(-5*pi/6)*cos(-pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(2195*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (548),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 6) * cos(-pi) - sin(-pi) * cos((-5) * pi / 6) = -sin(-pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-5*pi/6) * cos(-pi) - sin(-pi) * cos(-5*pi/6),
{
have : sin(pi/6) = sin((-5*pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(6889*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (574),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_90 (h0 : cos(2*pi/3)≠ 0) (h1 : (-sin(pi/3)**2+cos(pi/3)**2)≠ 0) : sin(2*pi/3)/(-sin(pi/3)**2 + cos(pi/3)**2)=- sqrt( 3 ):=
begin
have : cos(2*pi/3) = -sin(pi/3) ** 2 + cos(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = sin(2*pi/3) / cos(2*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_91 : 1/2 - cos(155*pi/3)/2=1 - sin(pi/3) ** 2:=
begin
have : sin(155*pi/6) ** 2 = 1 / 2 - cos(155*pi/3) / 2,
{
have : cos(155*pi/3) = cos(2*(155*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(155 * pi / 6)) ** 2 = sin(155*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(155*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (12),
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


lemma Trigo_number_generalization_step2_92 (h0 : tan(345*pi/2)≠ 0) (h1 : cos((345*pi)/2)≠ 0) (h2 : ((1-cos(345*pi))/sin(345*pi))≠ 0) (h3 : sin(345*pi)≠ 0) (h4 : (1-cos(345*pi))≠ 0) : -sin(345*pi)/(1 - cos(345*pi))=tan(712*pi):=
begin
have : (-1) / ((1 - cos(345 * pi)) / sin(345 * pi)) = -sin(345*pi)/(1 - cos(345*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(345*pi/2) = ( 1 - cos(345*pi) ) / sin(345*pi),
{
have : tan(345*pi/2) = tan((345*pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(345 * pi / 2) = -1/tan(345*pi/2),
{
field_simp at *,
},
have : tan(-2*pi) = -1 / tan(345*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-2*pi) (174),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = tan(712*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (714),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_93 (h0 : sin(pi/5)≠ 0) (h1 : (4*sin(pi/5)**2)≠ 0) (h2 : (2*sin(pi/5))≠ 0) : (1 - cos(2*pi/5)**2)/(4*sin(pi/5)**2)=1 - sin(pi/5) ** 2:=
begin
have : sin(2*pi/5) ** 2 = 1 - cos(2*pi/5) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * pi / 5) / (2 * sin(pi / 5))) ** 2 = sin(2*pi/5)**2/(4*sin(pi/5)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = sin(2*pi/5) / ( 2 * sin(pi/5) ),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
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
have : cos(pi/5) ** 2 = 1 - sin(pi/5) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_94 (h0 : cos((4*pi)/2)≠ 0) (h1 : sin(4*pi)≠ 0) : (cos(879*pi) + 1)/sin(4*pi)=tan(149*pi):=
begin
have : (1 - -cos(879 * pi)) / sin(4 * pi) = (cos(879*pi) + 1)/sin(4*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = -cos(879*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (4*pi) (441),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(2*pi) = tan(149*pi),
{
rw tan_eq_tan_add_int_mul_pi (2*pi) (147),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_95 : sin(7481*pi/6)**2=1 - cos(11653*pi/6)**2:=
begin
have : cos(-pi/3) = sin(7481*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (623),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (-cos(11653 * pi / 6)) ** 2 = 1 - cos(11653*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = -cos(11653*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (971),
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


lemma Trigo_number_generalization_step2_96 : 4*sin(3370*pi/3)**3 - 3*sin(3370*pi/3)=0:=
begin
have : (-4) * (-sin(3370 * pi / 3)) ** 3 + 3 * -sin(3370 * pi / 3) = 4*sin(3370*pi/3)**3 - 3*sin(3370*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(3370*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (561),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_97 (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : sin(944*pi)/(2*cos(pi/2))=sin(3889*pi/2):=
begin
have : sin(pi) = sin(944*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (472),
focus{repeat {apply congr_arg _}},
simp,
ring,
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
have : sin(pi/2) = sin(3889*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (972),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_98 : 4*sin(3449*pi/6)**2*cos(pi/6)**2=1 - cos(pi/3) ** 2:=
begin
have : sin(pi/6) = sin(3449*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (287),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * sin(pi / 6) * cos(pi / 6)) ** 2 = 4*sin(pi/6)**2*cos(pi/6)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 = 1 - cos(pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_99 : -cos(637*pi/10)=-cos(6483*pi/10):=
begin
have : sin(2404*pi/5) = cos(6483*pi/10),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2404*pi/5) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/5) = -cos(637*pi/10),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = - sin(2404*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/5) (240),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_100 : (-(-4*sin(5*pi/7)**3 + 3*sin(5*pi/7))*sin(-pi/7) + cos(-pi/7)*cos(15*pi/7))*cos(-pi/6)=cos(13*pi/6) / 2 + cos(11*pi/6) / 2:=
begin
have : (-sin(-pi / 7) * ((-4) * sin(5 * pi / 7) ** 3 + 3 * sin(5 * pi / 7)) + cos(-pi / 7) * cos(15 * pi / 7)) * cos(-pi / 6) = (-(-4*sin(5*pi/7)**3 + 3*sin(5*pi/7))*sin(-pi/7) + cos(-pi/7)*cos(15*pi/7))*cos(-pi/6),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(15*pi/7) = -4 * sin(5*pi/7) ** 3 + 3 * sin(5*pi/7),
{
have : sin(15*pi/7) = sin(3*(5*pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(15 * pi / 7) * sin(-pi / 7) + cos(15 * pi / 7) * cos(-pi / 7)) * cos(-pi / 6) = (-sin(-pi/7)*sin(15*pi/7) + cos(-pi/7)*cos(15*pi/7))*cos(-pi/6),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(15*pi/7) * sin(-pi/7) + cos(15*pi/7) * cos(-pi/7),
{
have : cos(2*pi) = cos((15*pi/7) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) * cos(-pi/6) = cos(13*pi/6) / 2 + cos(11*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((2*pi) + (-pi/6)) = cos(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (-pi/6)) = cos(13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_101 : -4*cos(216*pi)**3 + 3*cos(216*pi)=- 1:=
begin
have : -(4 * cos(216 * pi) ** 3 - 3 * cos(216 * pi)) = -4*cos(216*pi)**3 + 3*cos(216*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(648*pi) = 4 * cos(216*pi) ** 3 - 3 * cos(216*pi),
{
have : cos(648*pi) = cos(3*(216*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(648*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (324),
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


lemma Trigo_number_generalization_step2_102 : -(1 - 2*sin(-pi/16)**2)*sin(1454*pi)=sin(9*pi/8) / 2 + sin(7*pi/8) / 2:=
begin
have : (1 - 2 * sin(-pi / 16) ** 2) * -sin(1454 * pi) = -(1 - 2*sin(-pi/16)**2)*sin(1454*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(1454*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (726),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * (1 - 2 * sin(-pi / 16) ** 2) = (1 - 2*sin(-pi/16)**2)*sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = 1 - 2 * sin(-pi/16) ** 2,
{
have : cos(-pi/8) = cos(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(-pi/8) = sin(9*pi/8) / 2 + sin(7*pi/8) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (-pi/8)) = sin(7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (-pi/8)) = sin(9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_103 (h0 : cos(-2*pi)≠ 0) : 2*cos(-pi)*cos(295*pi/2)=sin(-4*pi) / ( 2 * cos(-2*pi) ):=
begin
have : 2 * cos(295 * pi / 2) * cos(-pi) = 2*cos(-pi)*cos(295*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(295*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (73),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step2_104 : -cos(1184*pi/3)**2 + sin(1184*pi/3)**2=- cos(4006*pi/3):=
begin
have : -(-sin(1184 * pi / 3) ** 2 + cos(1184 * pi / 3) ** 2) = -cos(1184*pi/3)**2 + sin(1184*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2368*pi/3) = -sin(1184*pi/3) ** 2 + cos(1184*pi/3) ** 2,
{
have : cos(2368*pi/3) = cos(2*(1184*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(2368*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (394),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(4006*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (667),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_105 : sin(-145*pi/9)**2=1 / 2 - cos(2*pi/9) / 2:=
begin
have : (-sin((-145) * pi / 9)) ** 2 = sin(-145*pi/9)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3701*pi/18) = -sin(-145*pi/9),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3701*pi/18) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = cos(3701*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (102),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) ** 2 = 1 / 2 - cos(2*pi/9) / 2,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
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


lemma Trigo_number_generalization_step2_106 (h0 : sin(pi/12)≠ 0) (h1 : (2*sin(pi/12))≠ 0) : -sin(10843*pi/6)/(2*sin(pi/12))=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/6) = -sin(10843*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (903),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(pi/6) / ( 2 * sin(pi/12) ),
{
have : sin(pi/6) = sin(2*(pi/12)),
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
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_107 (h0 : cos(-11*pi/60)≠ 0) (h1 : (2*cos((-11)*pi/60))≠ 0) (h2 : cos(-11*pi/60)≠ 0) : -cos(-2*pi/15)*cos(pi/3) + sin(-2*pi/15)*sin(pi/3) + cos(-pi/6)=-sin(-11*pi/30)*sin(pi/60)/cos(-11*pi/60):=
begin
have : cos(-pi / 6) - (-sin((-2) * pi / 15) * sin(pi / 3) + cos((-2) * pi / 15) * cos(pi / 3)) = -cos(-2*pi/15)*cos(pi/3) + sin(-2*pi/15)*sin(pi/3) + cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -sin(-2*pi/15) * sin(pi/3) + cos(-2*pi/15) * cos(pi/3),
{
have : cos(pi/5) = cos((-2*pi/15) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * (sin((-11) * pi / 30) / (2 * cos((-11) * pi / 60))) * sin(pi / 60) = -sin(-11*pi/30)*sin(pi/60)/cos(-11*pi/60),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-11*pi/60) = sin(-11*pi/30) / ( 2 * cos(-11*pi/60) ),
{
have : sin(-11*pi/30) = sin(2*(-11*pi/60)),
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
have : cos(-pi/6) - cos(pi/5) = - 2 * sin(-11*pi/60) * sin(pi/60),
{
rw cos_sub_cos,
have : sin(((-pi/6) + (pi/5))/2) = sin(pi/60),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (pi/5))/2) = sin(-11*pi/60),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_108 (h0 : cos(pi/8)≠ 0) (h1 : (1-tan(pi/8)**2)≠ 0) (h2 : cos((pi/4)/2)≠ 0) (h3 : ((-(1-cos(pi/4))**2/sin(pi/4)**2+1)*sin(pi/4))≠ 0) (h4 : sin(pi/4)≠ 0) (h5 : (1-((1-cos(pi/4))/sin(pi/4))**2)≠ 0) : 2*(1 - cos(pi/4))/((-(1 - cos(pi/4))**2/sin(pi/4)**2 + 1)*sin(pi/4))=1:=
begin
have : 2 * ((1 - cos(pi / 4)) / sin(pi / 4)) / (1 - ((1 - cos(pi / 4)) / sin(pi / 4)) ** 2) = 2*(1 - cos(pi/4))/((-(1 - cos(pi/4))**2/sin(pi/4)**2 + 1)*sin(pi/4)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = ( 1 - cos(pi/4) ) / sin(pi/4),
{
have : tan(pi/8) = tan((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 2 * tan(pi/8) / ( 1 - tan(pi/8) ** 2 ),
{
have : tan(pi/4) = tan(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_109 (h0 : cos((-2*pi/3)/2)≠ 0) (h1 : sin((-2)*pi/3)≠ 0) (h2 : sin(-2*pi/3)≠ 0) (h3 : cos(-2*pi/3)≠ 0) (h4 : sin(-4*pi/3)≠ 0) (h5 : (2*cos((-2)*pi/3))≠ 0) (h6 : (sin((-4)*pi/3)/(2*cos((-2)*pi/3)))≠ 0) : 2*(1 - cos(-2*pi/3))*cos(-2*pi/3)/sin(-4*pi/3)=- 1 / tan(3103*pi/6):=
begin
have : (1 - cos((-2) * pi / 3)) / (sin((-4) * pi / 3) / (2 * cos((-2) * pi / 3))) = 2*(1 - cos(-2*pi/3))*cos(-2*pi/3)/sin(-4*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = sin(-4*pi/3) / ( 2 * cos(-2*pi/3) ),
{
have : sin(-4*pi/3) = sin(2*(-2*pi/3)),
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
have : tan(-pi/3) = - 1 / tan(3103*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (517),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_110 (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) (h2 : (2*(-sin(pi/4)**2+cos(pi/4)**2))≠ 0) : sin(pi)/(2*(-sin(pi/4)**2 + cos(pi/4)**2))=1:=
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_111 : -1 + 2*sin(11471*pi/6)**2=- 1 / 2:=
begin
have : -1 + 2 * (-sin(11471 * pi / 6)) ** 2 = -1 + 2*sin(11471*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(11471*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (955),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 3) ** 2 - 1 = -1 + 2*cos(pi/3)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_112 : -4*sin(pi/18)**3 + 3*sin(pi/18)=-sin(-3305*pi/6):=
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
have : -sin((-3305) * pi / 6) = -sin(-3305*pi/6),
{
field_simp at *,
},
have : cos(4861*pi/3) = -sin(-3305*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4861*pi/3) (534),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = cos(4861*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (810),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_113 : cos(21317*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -cos(21317 * pi / 12) = cos(21317*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(12287*pi/12) = -cos(21317*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (12287*pi/12) (376),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(12287*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (512),
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


lemma Trigo_number_generalization_step2_114 : sin(4766*pi/7)=-sin(-2*pi)*cos(pi/7) + sin(-13*pi/7)/2 - sin(-15*pi/7)/2:=
begin
have : sin(15*pi/7) = sin(4766*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (15*pi/7) (341),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-15) * pi / 7) / 2 + sin((-13) * pi / 7) / 2 - sin((-2) * pi) * cos(pi / 7) = -sin(-2*pi)*cos(pi/7) + sin(-13*pi/7)/2 - sin(-15*pi/7)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) * cos(-2*pi) = -sin(-15*pi/7) / 2 + sin(-13*pi/7) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-2*pi) + (pi/7)) = sin(-13*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi/7)) = sin(-15*pi/7),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : (sin(pi/7) * cos(-2*pi)) = sin(pi/7)*cos(-2*pi),
{
ring,
},
have : sin(15*pi/7) = sin(pi/7) * cos(-2*pi) - sin(-2*pi) * cos(pi/7),
{
have : sin(15*pi/7) = sin((pi/7) - (-2*pi)),
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


lemma Trigo_number_generalization_step2_115 (h0 : cos(-pi/8)≠ 0) (h1 : (2*cos(-pi/8))≠ 0) (h2 : (2*sin(13139*pi/8))≠ 0) : sin(-pi/4)/(2*sin(13139*pi/8))=- cos(4829*pi/8):=
begin
have : cos(-pi/8) = sin(13139*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/8) (821),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(-pi/4) / ( 2 * cos(-pi/8) ),
{
have : sin(-pi/4) = sin(2*(-pi/8)),
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
have : sin(-pi/8) = - cos(4829*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (301),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_116 : sin(5*pi/4)=-sin(pi/4)*cos(98*pi) + sin(-pi)*cos(6021*pi/4):=
begin
have : -sin(pi / 4) * cos(98 * pi) - sin(-pi) * -cos(6021 * pi / 4) = -sin(pi/4)*cos(98*pi) + sin(-pi)*cos(6021*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = -cos(6021*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (752),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 4) * -cos(98 * pi) - sin(-pi) * cos(pi / 4) = -sin(pi/4)*cos(98*pi) - sin(-pi)*cos(pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -cos(98*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/4) = sin(pi/4) * cos(-pi) - sin(-pi) * cos(pi/4),
{
have : sin(5*pi/4) = sin((pi/4) - (-pi)),
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


lemma Trigo_number_generalization_step2_117 : (sin(535*pi)*cos(-pi/4) - sin(-pi/4)*sin(pi/2))*sin(pi/8)=- sin(pi/8) / 2 + sin(3*pi/8) / 2:=
begin
have : (cos(-pi / 4) * sin(535 * pi) - sin(-pi / 4) * sin(pi / 2)) * sin(pi / 8) = (sin(535*pi)*cos(-pi/4) - sin(-pi/4)*sin(pi/2))*sin(pi/8),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(535*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (267),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 8) * (-sin(-pi / 4) * sin(pi / 2) + cos(-pi / 4) * cos(pi / 2)) = (cos(-pi/4)*cos(pi/2) - sin(-pi/4)*sin(pi/2))*sin(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(-pi/4) * sin(pi/2) + cos(-pi/4) * cos(pi/2),
{
have : cos(pi/4) = cos((-pi/4) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) * cos(pi/4) = - sin(pi/8) / 2 + sin(3*pi/8) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/4) + (pi/8)) = sin(3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/4) - (pi/8)) = sin(pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_118 : -sin(11228*pi/15)=sin(-pi/3)*cos(-pi/5) + (-3*cos(-pi/9) + 4*cos(-pi/9)**3)*sin(-pi/5):=
begin
have : sin(-8*pi/15) = -sin(11228*pi/15),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-8*pi/15) (374),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 5) * (4 * cos(-pi / 9) ** 3 - 3 * cos(-pi / 9)) + sin(-pi / 3) * cos(-pi / 5) = sin(-pi/3)*cos(-pi/5) + (-3*cos(-pi/9) + 4*cos(-pi/9)**3)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-8*pi/15) = sin(-pi/5) * cos(-pi/3) + sin(-pi/3) * cos(-pi/5),
{
have : sin(-8*pi/15) = sin((-pi/5) + (-pi/3)),
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


lemma Trigo_number_generalization_step2_119 : sin(pi/8) ** 2=1 - cos(4647*pi/8)**2:=
begin
have : 1 - (-cos(4647 * pi / 8)) ** 2 = 1 - cos(4647*pi/8)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2257*pi/8) = -cos(4647*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2257*pi/8) (431),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = cos(2257*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/8) (141),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) ** 2 = 1 - cos(pi/8) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_120 (h0 : tan(85*pi/4)≠ 0) (h1 : cos(85*pi/8)≠ 0) (h2 : (2*tan(85*pi/8))≠ 0) (h3 : (2*tan(85*pi/8)/(1-tan(85*pi/8)**2))≠ 0) (h4 : (1-tan(85*pi/8)**2)≠ 0) : -(1 - tan(85*pi/8)**2)/(2*tan(85*pi/8))=- 1:=
begin
have : (-1) / (2 * tan(85 * pi / 8) / (1 - tan(85 * pi / 8) ** 2)) = -(1 - tan(85*pi/8)**2)/(2*tan(85*pi/8)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(85*pi/4) = 2 * tan(85*pi/8) / ( 1 - tan(85*pi/8) ** 2 ),
{
have : tan(85*pi/4) = tan(2*(85*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(85 * pi / 4) = -1/tan(85*pi/4),
{
field_simp at *,
},
have : tan(3*pi/4) = -1 / tan(85*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (3*pi/4) (20),
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


lemma Trigo_number_generalization_step2_121 (h0 : sin(-pi/9)≠ 0) (h1 : (2*sin(-pi/9)**3)≠ 0) (h2 : (2*sin(-pi/9))≠ 0) : -3*sin(-2*pi/9)/(2*sin(-pi/9)) + sin(-2*pi/9)**3/(2*sin(-pi/9)**3)=1 - 2 * sin(-pi/6) ** 2:=
begin
have : (-3) * (sin((-2) * pi / 9) / (2 * sin(-pi / 9))) + 4 * (sin((-2) * pi / 9) / (2 * sin(-pi / 9))) ** 3 = -3*sin(-2*pi/9)/(2*sin(-pi/9)) + sin(-2*pi/9)**3/(2*sin(-pi/9)**3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = sin(-2*pi/9) / ( 2 * sin(-pi/9) ),
{
have : sin(-2*pi/9) = sin(2*(-pi/9)),
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


lemma Trigo_number_generalization_step2_122 : sin(1442*pi/3)=1 - 2*cos(2167*pi/12)**2:=
begin
have : -(2 * cos(2167 * pi / 12) ** 2 - 1) = 1 - 2*cos(2167*pi/12)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2167*pi/6) = 2 * cos(2167*pi/12) ** 2 - 1,
{
have : cos(2167*pi/6) = cos(2*(2167*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(1442*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (240),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(2167*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (180),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_123 : sin(-pi)*cos(13*pi/12) + (1 - 2*sin(-pi/2)**2)*sin(13*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(-pi) * cos(13 * pi / 12) + sin(13 * pi / 12) * (1 - 2 * sin(-pi / 2) ** 2) = sin(-pi)*cos(13*pi/12) + (1 - 2*sin(-pi/2)**2)*sin(13*pi/12),
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
have : sin(13 * pi / 12) * cos(-pi) + sin(-pi) * cos(13 * pi / 12) = sin(-pi)*cos(13*pi/12) + sin(13*pi/12)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(13*pi/12) * cos(-pi) + sin(-pi) * cos(13*pi/12),
{
have : sin(pi/12) = sin((13*pi/12) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_124 : -sin(46632*pi/35)=sin(-pi/5)*cos(pi/7) - sin(pi/7)*sin(7687*pi/10):=
begin
have : sin(-12*pi/35) = -sin(46632*pi/35),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-12*pi/35) (666),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = sin(7687*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/5) (384),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-12*pi/35) = sin(-pi/5) * cos(pi/7) - sin(pi/7) * cos(-pi/5),
{
have : sin(-12*pi/35) = sin((-pi/5) - (pi/7)),
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


lemma Trigo_number_generalization_step2_125 : -sin(10103*pi/24)*cos(-pi/8) - sin(-pi/8)*cos(-pi/24)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(-pi/24) = -sin(10103*pi/24),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/24) (210),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(-pi/24) * cos(-pi/8) - sin(-pi/8) * cos(-pi/24),
{
have : sin(pi/12) = sin((-pi/24) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_126 : sin(-pi/5)*cos(4489*pi/30) - sin(4489*pi/30)*cos(-pi/5)=1 / 2:=
begin
have : -(sin(4489 * pi / 30) * cos(-pi / 5) - sin(-pi / 5) * cos(4489 * pi / 30)) = sin(-pi/5)*cos(4489*pi/30) - sin(4489*pi/30)*cos(-pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(899*pi/6) = sin(4489*pi/30) * cos(-pi/5) - sin(-pi/5) * cos(4489*pi/30),
{
have : sin(899*pi/6) = sin((4489*pi/30) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(899*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (74),
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


lemma Trigo_number_generalization_step2_127 : -3*cos(67103*pi/36) + 4*cos(67103*pi/36)**3=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-3) * cos(67103 * pi / 36) + 4 * cos(67103 * pi / 36) ** 3 = -3*cos(67103*pi/36) + 4*cos(67103*pi/36)**3,
{
field_simp at *,
},
have : cos(pi/36) = cos(67103*pi/36),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/36) (932),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36) = -3*cos(pi/36) + 4*cos(pi/36)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = 4 * cos(pi/36) ** 3 - 3 * cos(pi/36),
{
have : cos(pi/12) = cos(3*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_128 : -1 + 2*(-3*cos(pi/6) + 4*cos(pi/6)**3)**2=- 1:=
begin
have : -1 + 2 * (4 * cos(pi / 6) ** 3 - 3 * cos(pi / 6)) ** 2 = -1 + 2*(-3*cos(pi/6) + 4*cos(pi/6)**3)**2,
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
have : 2 * cos(pi / 2) ** 2 - 1 = -1 + 2*cos(pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 2 * cos(pi/2) ** 2 - 1,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_129 (h0 : cos(pi/6)≠ 0) (h1 : (1-tan(pi/6)**2)≠ 0) (h2 : cos(-pi/12)≠ 0) (h3 : cos(-pi/4)≠ 0) (h4 : (1+tan(-pi/12)*tan(-pi/4))≠ 0) (h5 : ((-(tan(-pi/12)-tan(-pi/4))**2/(tan(-pi/4)*tan(-pi/12)+1)**2+1)*(tan(-pi/4)*tan(-pi/12)+1))≠ 0) (h6 : (1-((tan(-pi/12)-tan(-pi/4))/(1+tan(-pi/12)*tan(-pi/4)))**2)≠ 0) (h7 : (tan(-pi/4)*tan(-pi/12)+1)≠ 0) : 2*(tan(-pi/12) - tan(-pi/4))/((-(tan(-pi/12) - tan(-pi/4))**2/(tan(-pi/4)*tan(-pi/12) + 1)**2 + 1)*(tan(-pi/4)*tan(-pi/12) + 1))=sqrt( 3 ):=
begin
have : 2 * ((tan(-pi / 12) - tan(-pi / 4)) / (1 + tan(-pi / 12) * tan(-pi / 4))) / (1 - ((tan(-pi / 12) - tan(-pi / 4)) / (1 + tan(-pi / 12) * tan(-pi / 4))) ** 2) = 2*(tan(-pi/12) - tan(-pi/4))/((-(tan(-pi/12) - tan(-pi/4))**2/(tan(-pi/4)*tan(-pi/12) + 1)**2 + 1)*(tan(-pi/4)*tan(-pi/12) + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(-pi/12) - tan(-pi/4) ) / ( 1 + tan(-pi/12) * tan(-pi/4) ),
{
have : tan(pi/6) = tan((-pi/12) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 2 * tan(pi/6) / ( 1 - tan(pi/6) ** 2 ),
{
have : tan(pi/3) = tan(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_130 : 1 - 2*cos(5363*pi/4)**2=0:=
begin
have : 1 - 2 * (-cos(5363 * pi / 4)) ** 2 = 1 - 2*cos(5363*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(5363*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (670),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_131 : cos(pi/2)*cos(710*pi) - sin(pi/2)*sin(710*pi)=0:=
begin
have : -sin(710 * pi) * sin(pi / 2) + cos(710 * pi) * cos(pi / 2) = cos(pi/2)*cos(710*pi) - sin(pi/2)*sin(710*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1421*pi/2) = -sin(710*pi) * sin(pi/2) + cos(710*pi) * cos(pi/2),
{
have : cos(1421*pi/2) = cos((710*pi) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(1421*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (354),
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


lemma Trigo_number_generalization_step2_132 (h0 : cos(-5*pi/3)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (tan(-2*pi)*tan(-5*pi/3)+1)≠ 0) (h3 : (1+tan((-5)*pi/3)*tan((-2)*pi))≠ 0) (h4 : cos((-5)*pi/3)≠ 0) (h5 : (tan((-2)*pi)*(sin((-5)*pi/3)/cos((-5)*pi/3))+1)≠ 0) (h6 : (sin(-5*pi/3)*tan(-2*pi)/cos(-5*pi/3)+1)≠ 0) (h7 : cos(-5*pi/3)≠ 0) : (-tan(-2*pi) + sin(-5*pi/3)/cos(-5*pi/3))/(sin(-5*pi/3)*tan(-2*pi)/cos(-5*pi/3) + 1)=sqrt( 3 ):=
begin
have : (-tan((-2) * pi) + sin((-5) * pi / 3) / cos((-5) * pi / 3)) / (tan((-2) * pi) * (sin((-5) * pi / 3) / cos((-5) * pi / 3)) + 1) = (-tan(-2*pi) + sin(-5*pi/3)/cos(-5*pi/3))/(sin(-5*pi/3)*tan(-2*pi)/cos(-5*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-5*pi/3) = sin(-5*pi/3) / cos(-5*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (tan((-5) * pi / 3) - tan((-2) * pi)) / (1 + tan((-5) * pi / 3) * tan((-2) * pi)) = (-tan(-2*pi) + tan(-5*pi/3))/(tan(-2*pi)*tan(-5*pi/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( tan(-5*pi/3) - tan(-2*pi) ) / ( 1 + tan(-5*pi/3) * tan(-2*pi) ),
{
have : tan(pi/3) = tan((-5*pi/3) - (-2*pi)),
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


lemma Trigo_number_generalization_step2_133 (h0 : cos(pi/2)≠ 0) (h1 : (1-tan(pi/2)**2)≠ 0) (h2 : tan(770*pi)≠ 0) (h3 : ((1-1/tan(770*pi)**2)*tan(770*pi))≠ 0) (h4 : (1-(1/tan(770*pi))**2)≠ 0) : 2/((1 - 1/tan(770*pi)**2)*tan(770*pi))=0:=
begin
have : 2 * (1 / tan(770 * pi)) / (1 - (1 / tan(770 * pi)) ** 2) = 2/((1 - 1/tan(770*pi)**2)*tan(770*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = 1 / tan(770*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/2) (770),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 2 * tan(pi/2) / ( 1 - tan(pi/2) ** 2 ),
{
have : tan(pi) = tan(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_134 (h0 : tan((-953)*pi/3)≠ 0) (h1 : tan(-953*pi/3)≠ 0) : 1/tan(-953*pi/3)=sqrt( 3 ) / 3:=
begin
have : 1 / tan((-953) * pi / 3) = 1/tan(-953*pi/3),
{
field_simp at *,
},
have : tan(2287*pi/6) = 1 / tan(-953*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2287*pi/6) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(2287*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (381),
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


lemma Trigo_number_generalization_step2_135 : -sin(3597*pi/10)=- sin(11437*pi/10):=
begin
have : sin(1137*pi/10) = sin(3597*pi/10),
{
rw sin_eq_sin_add_int_mul_two_pi (1137*pi/10) (123),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -sin(1137*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = - sin(11437*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (571),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_136 : (1 - 2*sin(-5*pi/12)**2)*sin(pi/3) + sin(-5*pi/6)*cos(pi/3)=- 4 * sin(-pi/6) ** 3 + 3 * sin(-pi/6):=
begin
have : sin(pi / 3) * (1 - 2 * sin((-5) * pi / 12) ** 2) + sin((-5) * pi / 6) * cos(pi / 3) = (1 - 2*sin(-5*pi/12)**2)*sin(pi/3) + sin(-5*pi/6)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/6) = 1 - 2 * sin(-5*pi/12) ** 2,
{
have : cos(-5*pi/6) = cos(2*(-5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 6) * cos(pi / 3) + sin(pi / 3) * cos((-5) * pi / 6) = sin(pi/3)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-5*pi/6) * cos(pi/3) + sin(pi/3) * cos(-5*pi/6),
{
have : sin(-pi/2) = sin((-5*pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step2_137 : -3*cos(889*pi/3) + 4*cos(889*pi/3)**3=sin(635*pi/2):=
begin
have : (-3) * cos(889 * pi / 3) + 4 * cos(889 * pi / 3) ** 3 = -3*cos(889*pi/3) + 4*cos(889*pi/3)**3,
{
field_simp at *,
},
have : cos(pi/3) = cos(889*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (148),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(pi / 3) ** 3 - 3 * cos(pi / 3) = -3*cos(pi/3) + 4*cos(pi/3)**3,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(635*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (159),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_138 : -sin(-23*pi/6)/2 + sin(pi/6)/2 + sin(-11*pi/6)*cos(-2*pi)=1 / 2:=
begin
have : -(-sin(pi / 6) / 2 + sin((-23) * pi / 6) / 2) + sin((-11) * pi / 6) * cos((-2) * pi) = -sin(-23*pi/6)/2 + sin(pi/6)/2 + sin(-11*pi/6)*cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-11*pi/6) = -sin(pi/6) / 2 + sin(-23*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-11*pi/6) + (-2*pi)) = sin(-23*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-11*pi/6) - (-2*pi)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(-2*pi) * cos(-11*pi/6)) = -sin(-2*pi)*cos(-11*pi/6),
{
ring,
},
conv {to_lhs, rw this,},
have : sin((-11) * pi / 6) * cos((-2) * pi) - sin((-2) * pi) * cos((-11) * pi / 6) = -sin(-2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(-2*pi),
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
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_139 : -sin(-pi/6)*cos(10217*pi/12) + sin(7*pi/12)*cos(-pi/6)=sin(-pi/4) * cos(pi) + sin(pi) * cos(-pi/4):=
begin
have : cos(7*pi/12) = cos(10217*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (7*pi/12) (426),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 12) * cos(-pi / 6) - sin(-pi / 6) * cos(7 * pi / 12) = -sin(-pi/6)*cos(7*pi/12) + sin(7*pi/12)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(7*pi/12) * cos(-pi/6) - sin(-pi/6) * cos(7*pi/12),
{
have : sin(3*pi/4) = sin((7*pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(-pi/4) * cos(pi) + sin(pi) * cos(-pi/4),
{
have : sin(3*pi/4) = sin((-pi/4) + (pi)),
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


lemma Trigo_number_generalization_step2_140 (h0 : cos(-pi)≠ 0) (h1 : (sin((-8)*pi/7)*sin(-pi/7)+cos((-8)*pi/7)*cos(-pi/7))≠ 0) (h2 : (cos(-8*pi/7)*cos(-pi/7)+sin(-8*pi/7)*sin(-pi/7))≠ 0) : tan(-pi)=cos(241*pi/2)/(cos(-8*pi/7)*cos(-pi/7) + sin(-8*pi/7)*sin(-pi/7)):=
begin
have : cos(241 * pi / 2) / (sin((-8) * pi / 7) * sin(-pi / 7) + cos((-8) * pi / 7) * cos(-pi / 7)) = cos(241*pi/2)/(cos(-8*pi/7)*cos(-pi/7) + sin(-8*pi/7)*sin(-pi/7)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(-8*pi/7) * sin(-pi/7) + cos(-8*pi/7) * cos(-pi/7),
{
have : cos(-pi) = cos((-8*pi/7) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(241*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi) = sin(-pi) / cos(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_141 : 4*sin(707*pi/6)**3 - 3*sin(707*pi/6)=- cos(1335*pi):=
begin
have : cos(2*pi/3) = sin(707*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (59),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(2*pi) = - cos(1335*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (668),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_142 : -1 + 2*sin(1613*pi/4)**2=cos(2511*pi/2):=
begin
have : -(1 - 2 * sin(1613 * pi / 4) ** 2) = -1 + 2*sin(1613*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1613*pi/2) = 1 - 2 * sin(1613*pi/4) ** 2,
{
have : cos(1613*pi/2) = cos(2*(1613*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(1613*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (403),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(2511*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (628),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_143 : cos(pi/3)*cos(5885*pi/6) + sin(pi/3)*sin(5885*pi/6)=0:=
begin
have : sin(5885 * pi / 6) * sin(pi / 3) + cos(5885 * pi / 6) * cos(pi / 3) = cos(pi/3)*cos(5885*pi/6) + sin(pi/3)*sin(5885*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1961*pi/2) = sin(5885*pi/6) * sin(pi/3) + cos(5885*pi/6) * cos(pi/3),
{
have : cos(1961*pi/2) = cos((5885*pi/6) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(1961*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (490),
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


lemma Trigo_number_generalization_step2_144 : cos(-pi/3)*cos(1445*pi/3) - sin(-pi/3)*cos(pi/6)=1:=
begin
have : cos(1445 * pi / 3) * cos(-pi / 3) - sin(-pi / 3) * cos(pi / 6) = cos(-pi/3)*cos(1445*pi/3) - sin(-pi/3)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(1445*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (240),
focus{repeat {apply congr_arg _}},
simp,
ring,
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_145 : sin(1205*pi)*sin(3071*pi/2)=cos(5*pi/2) / 2 + cos(-3*pi/2) / 2:=
begin
have : -sin(1205 * pi) * -sin(3071 * pi / 2) = sin(1205*pi)*sin(3071*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(3071*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (768),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(1205 * pi) * cos((-2) * pi) = -sin(1205*pi)*cos(-2*pi),
{
field_simp at *,
},
have : cos(pi/2) = -sin(1205*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (602),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) * cos(-2*pi) = cos(5*pi/2) / 2 + cos(-3*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((pi/2) + (-2*pi)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (-2*pi)) = cos(5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_146 : -sin(4659*pi/4)=- sin(5659*pi/4):=
begin
have : sin(3755*pi/4) = sin(4659*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (3755*pi/4) (113),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -sin(3755*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (469),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = - sin(5659*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (707),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_147 (h0 : sin(10751*pi/14)≠ 0) (h1 : (2*sin(10751*pi/14))≠ 0) : sin(10751*pi/7)/(2*sin(10751*pi/14))=- 4 * sin(pi/7) ** 3 + 3 * sin(pi/7):=
begin
have : cos(10751*pi/14) = sin(10751*pi/7) / ( 2 * sin(10751*pi/14) ),
{
have : sin(10751*pi/7) = sin(2*(10751*pi/14)),
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
have : sin(3*pi/7) = cos(10751*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/7) (383),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/7) = - 4 * sin(pi/7) ** 3 + 3 * sin(pi/7),
{
have : sin(3*pi/7) = sin(3*(pi/7)),
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


lemma Trigo_number_generalization_step2_148 : (-1 + 2*sin(12907*pi/8)**2)*cos(pi)=cos(3*pi/4) / 2 + cos(5*pi/4) / 2:=
begin
have : (-1 + 2 * (-sin(12907 * pi / 8)) ** 2) * cos(pi) = (-1 + 2*sin(12907*pi/8)**2)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(12907*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (806),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * (2 * cos(pi / 8) ** 2 - 1) = (-1 + 2*cos(pi/8)**2)*cos(pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = 2 * cos(pi/8) ** 2 - 1,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * cos(pi/4) = cos(3*pi/4) / 2 + cos(5*pi/4) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (pi/4)) = cos(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (pi/4)) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_149 : cos(2*pi)=-2*sin(4843*pi/4)*cos(4843*pi/4):=
begin
have : -(2 * sin(4843 * pi / 4) * cos(4843 * pi / 4)) = -2*sin(4843*pi/4)*cos(4843*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(4843*pi/2) = 2 * sin(4843*pi/4) * cos(4843*pi/4),
{
have : sin(4843*pi/2) = sin(2*(4843*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(2231*pi/2) = sin(4843*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (2231*pi/2) (653),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(2231*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (558),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_150 : -cos(pi/8)**2 + sin(pi/8)**2 + sin(-13*pi/36)*sin(-pi/9) + cos(-13*pi/36)*cos(-pi/9)=- 2 * sin(-pi/4) * sin(0):=
begin
have : -cos(pi / 8) ** 2 + sin(pi / 8) ** 2 + (sin((-13) * pi / 36) * sin(-pi / 9) + cos((-13) * pi / 36) * cos(-pi / 9)) = -cos(pi/8)**2 + sin(pi/8)**2 + sin(-13*pi/36)*sin(-pi/9) + cos(-13*pi/36)*cos(-pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(-13*pi/36) * sin(-pi/9) + cos(-13*pi/36) * cos(-pi/9),
{
have : cos(-pi/4) = cos((-13*pi/36) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi / 4) - (-sin(pi / 8) ** 2 + cos(pi / 8) ** 2) = -cos(pi/8)**2 + sin(pi/8)**2 + cos(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(pi/8) ** 2 + cos(pi/8) ** 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) - cos(pi/4) = - 2 * sin(-pi/4) * sin(0),
{
rw cos_sub_cos,
have : sin(((-pi/4) + (pi/4))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/4) - (pi/4))/2) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_151 : -tan(781*pi)=tan(245*pi):=
begin
have : tan(516*pi) = tan(781*pi),
{
rw tan_eq_tan_add_int_mul_pi (516*pi) (265),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = -tan(516*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (518),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = tan(245*pi),
{
rw tan_eq_tan_add_int_mul_pi (2*pi) (243),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_152 (h0 : tan(401*pi/2)≠ 0) (h1 : tan(438*pi)≠ 0) (h2 : ((-1)/tan(438*pi))≠ 0) : tan(438*pi)=tan(211*pi):=
begin
have : (-1) / ((-1) / tan(438 * pi)) = tan(438*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(401*pi/2) = -1 / tan(438*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (401*pi/2) (237),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(401 * pi / 2) = -1/tan(401*pi/2),
{
field_simp at *,
},
have : tan(-pi) = -1 / tan(401*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (201),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(211*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (212),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_153 (h0 : cos(-pi)≠ 0) : cos(-373*pi/2)=sin(-2*pi) / ( 2 * cos(-pi) ):=
begin
have : cos((-373) * pi / 2) = cos(-373*pi/2),
{
field_simp at *,
},
have : cos(2153*pi/2) = cos(-373*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2153*pi/2) (445),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(2153*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (538),
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


lemma Trigo_number_generalization_step2_154 : cos(41261*pi/28)=sin(-pi/7)*cos(pi/4) + sin(1625*pi/4)*cos(-pi/7):=
begin
have : sin(1625 * pi / 4) * cos(-pi / 7) + sin(-pi / 7) * cos(pi / 4) = sin(-pi/7)*cos(pi/4) + sin(1625*pi/4)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) = sin(1625*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (203),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi/28) = cos(41261*pi/28),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/28) (736),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/28) = sin(pi/4) * cos(-pi/7) + sin(-pi/7) * cos(pi/4),
{
have : sin(3*pi/28) = sin((pi/4) + (-pi/7)),
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


lemma Trigo_number_generalization_step2_155 : -sin(pi/3)*cos(5*pi/24) + sin(-pi/9) + sin(5*pi/24)*cos(pi/3)=sin(-pi/8) + sin(-pi/9):=
begin
have : sin(-pi / 9) + (sin(5 * pi / 24) * cos(pi / 3) - sin(pi / 3) * cos(5 * pi / 24)) = -sin(pi/3)*cos(5*pi/24) + sin(-pi/9) + sin(5*pi/24)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(5*pi/24) * cos(pi/3) - sin(pi/3) * cos(5*pi/24),
{
have : sin(-pi/8) = sin((5*pi/24) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sin(-pi / 8) / 2 + sin(-pi / 9) / 2) = sin(-pi/8) + sin(-pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-17*pi/144) * cos(pi/144) = sin(-pi/8) / 2 + sin(-pi/9) / 2,
{
rw sin_mul_cos,
have : sin((-17*pi/144) + (pi/144)) = sin(-pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-17*pi/144) - (pi/144)) = sin(-pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-17*pi/144) * cos(pi/144)) = 2*sin(-17*pi/144)*cos(pi/144),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi/9) + sin(-pi/8) = 2 * sin(-17*pi/144) * cos(pi/144),
{
rw sin_add_sin,
have : sin(((-pi/9) + (-pi/8))/2) = sin(-17*pi/144),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (-pi/8))/2) = cos(pi/144),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_156 : -tan(-4861*pi/12)=2 - sqrt( 3 ):=
begin
have : -tan((-4861) * pi / 12) = -tan(-4861*pi/12),
{
field_simp at *,
},
have : tan(4993*pi/12) = -tan(-4861*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (4993*pi/12) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = tan(4993*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (416),
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


lemma Trigo_number_generalization_step2_157 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) : (sin(-pi/3)*sin(pi) - cos(-pi/3)*cos(pi) + 1)/sin(2*pi/3)=- tan(2774*pi/3):=
begin
have : (1 - (-sin(pi) * sin(-pi / 3) + cos(pi) * cos(-pi / 3))) / sin(2 * pi / 3) = (sin(-pi/3)*sin(pi) - cos(-pi/3)*cos(pi) + 1)/sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(pi) * sin(-pi/3) + cos(pi) * cos(-pi/3),
{
have : cos(2*pi/3) = cos((pi) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( 1 - cos(2*pi/3) ) / sin(2*pi/3),
{
have : tan(pi/3) = tan((2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = - tan(2774*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (925),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_158 : cos(4229*pi/2)=0:=
begin
have : - -cos(4229 * pi / 2) = cos(4229*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1352*pi) = -cos(4229*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1352*pi) (381),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(1352*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (675),
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


lemma Trigo_number_generalization_step2_159 : -sin(30091*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(7057*pi/12) = -sin(30091*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (7057*pi/12) (959),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = cos(7057*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/12) (294),
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


lemma Trigo_number_generalization_step2_160 : sin(-pi/5) * sin(-pi/7)=2*cos(94*pi/35)**3 - cos(-12*pi/35)/2 - 3*cos(94*pi/35)/2:=
begin
have : -cos((-12) * pi / 35) / 2 + (4 * cos(94 * pi / 35) ** 3 - 3 * cos(94 * pi / 35)) / 2 = 2*cos(94*pi/35)**3 - cos(-12*pi/35)/2 - 3*cos(94*pi/35)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(282*pi/35) = 4 * cos(94*pi/35) ** 3 - 3 * cos(94*pi/35),
{
have : cos(282*pi/35) = cos(3*(94*pi/35)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : cos(282 * pi / 35) / 2 - cos((-12) * pi / 35) / 2 = -cos(-12*pi/35)/2 + cos(282*pi/35)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/35) = cos(282*pi/35),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi/35) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/5) * sin(-pi/7) = cos(-2*pi/35) / 2 - cos(-12*pi/35) / 2,
{
rw sin_mul_sin,
have : cos((-pi/5) + (-pi/7)) = cos(-12*pi/35),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (-pi/7)) = cos(-2*pi/35),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_161 (h0 : cos(-5*pi/12)≠ 0) (h1 : cos(-pi/6)≠ 0) (h2 : (1+tan(-5*pi/12)*tan(-pi/6))≠ 0) (h3 : (1+tan((-5)*pi/12)*tan(-pi/6))≠ 0) (h4 : cos(-5*pi/12)≠ 0) (h5 : cos(-pi/6)≠ 0) (h6 : ((1+tan(-5*pi/12)*tan(-pi/6))*cos(-5*pi/12)*cos(-pi/6))≠ 0) (h7 : (cos((-5)*pi/12)*cos(-pi/6))≠ 0) : sin(-pi/4)/((1 + tan(-5*pi/12)*tan(-pi/6))*cos(-5*pi/12)*cos(-pi/6))=- 1 / tan(2845*pi/4):=
begin
have : sin(-pi / 4) / (cos((-5) * pi / 12) * cos(-pi / 6)) / (1 + tan((-5) * pi / 12) * tan(-pi / 6)) = sin(-pi/4)/((1 + tan(-5*pi/12)*tan(-pi/6))*cos(-5*pi/12)*cos(-pi/6)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-5*pi/12) - tan(-pi/6) = sin(-pi/4) / ( cos(-5*pi/12) * cos(-pi/6) ),
{
rw tan_sub_tan',
have : sin((-5*pi/12) - (-pi/6)) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan((-5) * pi / 12) - tan(-pi / 6)) / (1 + tan((-5) * pi / 12) * tan(-pi / 6)) = (tan(-5*pi/12) - tan(-pi/6))/(1 + tan(-5*pi/12)*tan(-pi/6)),
{
field_simp at *,
},
have : tan(-pi/4) = ( tan(-5*pi/12) - tan(-pi/6) ) / ( 1 + tan(-5*pi/12) * tan(-pi/6) ),
{
have : tan(-pi/4) = tan((-5*pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = - 1 / tan(2845*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/4) (711),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_162 : cos(-2554*pi/3)=- 1 / 2:=
begin
have : cos((-2554) * pi / 3) = cos(-2554*pi/3),
{
field_simp at *,
},
have : cos(5704*pi/3) = cos(-2554*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5704*pi/3) (525),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = cos(5704*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (951),
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


lemma Trigo_number_generalization_step2_163 (h0 : sin(pi/4)≠ 0) (h1 : (2*sin(pi/4))≠ 0) : -sin(2543*pi/4)=-sin(2475*pi/2)/(2*sin(pi/4)):=
begin
have : cos(pi/4) = -sin(2543*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (317),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(2475*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (618),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = sin(pi/2) / ( 2 * sin(pi/4) ),
{
have : sin(pi/2) = sin(2*(pi/4)),
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


lemma Trigo_number_generalization_step2_164 (h0 : tan((-399)*pi/4)≠ 0) (h1 : tan(-399*pi/4)≠ 0) : -1/tan(-399*pi/4)=1 / tan(2963*pi/4):=
begin
have : -(1 / tan((-399) * pi / 4)) = -1/tan(-399*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3341*pi/4) = 1 / tan(-399*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3341*pi/4) (735),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = -tan(3341*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/4) (835),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = 1 / tan(2963*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/4) (740),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_165 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : (cos(2*pi/3)+1)≠ 0) (h2 : (1+cos(2*pi/3))≠ 0) (h3 : (1-sin(1273*pi/6))≠ 0) (h4 : (-sin(1273*pi/6)+1)≠ 0) : sin(2*pi/3)/(1 - sin(1273*pi/6))=- tan(2432*pi/3):=
begin
have : sin(2 * pi / 3) / (-sin(1273 * pi / 6) + 1) = sin(2*pi/3)/(1 - sin(1273*pi/6)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(1273*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (105),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/3) = - tan(2432*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (811),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_166 : cos(3442*pi/3)**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : (-cos(3442 * pi / 3)) ** 2 = cos(3442*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1235*pi/3) = -cos(3442*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (1235*pi/3) (779),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(1235*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (206),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step2_167 : sin(pi/6) * sin(pi)=sin(5855*pi/3)/2 + sin(pi/9)*sin(19*pi/18)/2 - cos(pi/9)*cos(19*pi/18)/2:=
begin
have : sin(5855 * pi / 3) / 2 - (-sin(19 * pi / 18) * sin(pi / 9) + cos(19 * pi / 18) * cos(pi / 9)) / 2 = sin(5855*pi/3)/2 + sin(pi/9)*sin(19*pi/18)/2 - cos(pi/9)*cos(19*pi/18)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/6) = -sin(19*pi/18) * sin(pi/9) + cos(19*pi/18) * cos(pi/9),
{
have : cos(7*pi/6) = cos((19*pi/18) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/6) = sin(5855*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-5*pi/6) (976),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_168 : cos(6491*pi/14)=sin(3487*pi/7):=
begin
have : sin(4850*pi/7) = cos(6491*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4850*pi/7) (578),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(4850*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/7) (346),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(3487*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/7) (249),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_169 : -sin(-2*pi)*sin(6199*pi/6) - cos(-2*pi)*cos(6199*pi/6)=sqrt( 3 ) / 2:=
begin
have : -(sin(6199 * pi / 6) * sin((-2) * pi) + cos(6199 * pi / 6) * cos((-2) * pi)) = -sin(-2*pi)*sin(6199*pi/6) - cos(-2*pi)*cos(6199*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(6211*pi/6) = sin(6199*pi/6) * sin(-2*pi) + cos(6199*pi/6) * cos(-2*pi),
{
have : cos(6211*pi/6) = cos((6199*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(6211*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (517),
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


lemma Trigo_number_generalization_step2_170 : -cos(1273*pi)=sin(2341*pi/2):=
begin
have : cos(486*pi) = -cos(1273*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (486*pi) (393),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(486*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (242),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(2341*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (586),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_171 : -sin(11*pi/12)**2 + (-3*cos(11*pi/36) + 4*cos(11*pi/36)**3)**2=sin(-pi/6) * sin(-2*pi) + cos(-pi/6) * cos(-2*pi):=
begin
have : -sin(11 * pi / 12) ** 2 + (4 * cos(11 * pi / 36) ** 3 - 3 * cos(11 * pi / 36)) ** 2 = -sin(11*pi/12)**2 + (-3*cos(11*pi/36) + 4*cos(11*pi/36)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/12) = 4 * cos(11*pi/36) ** 3 - 3 * cos(11*pi/36),
{
have : cos(11*pi/12) = cos(3*(11*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/6) = -sin(11*pi/12) ** 2 + cos(11*pi/12) ** 2,
{
have : cos(11*pi/6) = cos(2*(11*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/6) = sin(-pi/6) * sin(-2*pi) + cos(-pi/6) * cos(-2*pi),
{
have : cos(11*pi/6) = cos((-pi/6) - (-2*pi)),
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


lemma Trigo_number_generalization_step2_172 (h0 : cos(23*pi/36)≠ 0) (h1 : cos(-pi/9)≠ 0) (h2 : (tan(-pi/9)*tan(23*pi/36)+1)≠ 0) (h3 : (1+tan(23*pi/36)*tan(-pi/9))≠ 0) (h4 : (sin(23*pi/36)*tan(-pi/9)/cos(23*pi/36)+1)≠ 0) (h5 : cos(23*pi/36)≠ 0) (h6 : (tan(-pi/9)*(sin(23*pi/36)/cos(23*pi/36))+1)≠ 0) : (sin(23*pi/36)/cos(23*pi/36) - tan(-pi/9))/(sin(23*pi/36)*tan(-pi/9)/cos(23*pi/36) + 1)=- 1:=
begin
have : (sin(23 * pi / 36) / cos(23 * pi / 36) - tan(-pi / 9)) / (tan(-pi / 9) * (sin(23 * pi / 36) / cos(23 * pi / 36)) + 1) = (sin(23*pi/36)/cos(23*pi/36) - tan(-pi/9))/(sin(23*pi/36)*tan(-pi/9)/cos(23*pi/36) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(23*pi/36) = sin(23*pi/36) / cos(23*pi/36),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (tan(23 * pi / 36) - tan(-pi / 9)) / (1 + tan(23 * pi / 36) * tan(-pi / 9)) = (tan(23*pi/36) - tan(-pi/9))/(tan(-pi/9)*tan(23*pi/36) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = ( tan(23*pi/36) - tan(-pi/9) ) / ( 1 + tan(23*pi/36) * tan(-pi/9) ),
{
have : tan(3*pi/4) = tan((23*pi/36) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_173 (h0 : (-sin(5*pi/8)*sin(-pi/2)+cos(5*pi/8)*cos(-pi/2))≠ 0) (h1 : (cos(-pi/2)*cos(5*pi/8)-sin(-pi/2)*sin(5*pi/8))≠ 0) (h2 : (cos(3191*pi/2)*cos(5*pi/8)-sin(-pi/2)*sin(5*pi/8))≠ 0) (h3 : (cos(5*pi/8)*cos(3191*pi/2)-sin(-pi/2)*sin(5*pi/8))≠ 0) : tan(pi/8)=sin(pi/8)/(cos(5*pi/8)*cos(3191*pi/2) - sin(-pi/2)*sin(5*pi/8)):=
begin
have : sin(pi / 8) / (cos(3191 * pi / 2) * cos(5 * pi / 8) - sin(-pi / 2) * sin(5 * pi / 8)) = sin(pi/8)/(cos(5*pi/8)*cos(3191*pi/2) - sin(-pi/2)*sin(5*pi/8)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = cos(3191*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (798),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 8) / (-sin(5 * pi / 8) * sin(-pi / 2) + cos(5 * pi / 8) * cos(-pi / 2)) = sin(pi/8)/(cos(-pi/2)*cos(5*pi/8) - sin(-pi/2)*sin(5*pi/8)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = -sin(5*pi/8) * sin(-pi/2) + cos(5*pi/8) * cos(-pi/2),
{
have : cos(pi/8) = cos((5*pi/8) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/8) = sin(pi/8) / cos(pi/8),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_174 : -2*sin(649*pi)*cos(649*pi)=0:=
begin
have : -(2 * sin(649 * pi) * cos(649 * pi)) = -2*sin(649*pi)*cos(649*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1298*pi) = 2 * sin(649*pi) * cos(649*pi),
{
have : sin(1298*pi) = sin(2*(649*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(1298*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (648),
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


lemma Trigo_number_generalization_step2_175 : (cos(pi/2)*cos(9*pi/14) + sin(pi/2)*sin(9*pi/14))*cos(-53*pi/126) - sin(-53*pi/126)*sin(pi/7)=sin(-pi/6) * sin(pi/9) + cos(-pi/6) * cos(pi/9):=
begin
have : cos((-53) * pi / 126) * (sin(9 * pi / 14) * sin(pi / 2) + cos(9 * pi / 14) * cos(pi / 2)) - sin((-53) * pi / 126) * sin(pi / 7) = (cos(pi/2)*cos(9*pi/14) + sin(pi/2)*sin(9*pi/14))*cos(-53*pi/126) - sin(-53*pi/126)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = sin(9*pi/14) * sin(pi/2) + cos(9*pi/14) * cos(pi/2),
{
have : cos(pi/7) = cos((9*pi/14) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-53) * pi / 126) * sin(pi / 7) + cos((-53) * pi / 126) * cos(pi / 7) = cos(-53*pi/126)*cos(pi/7) - sin(-53*pi/126)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/18) = -sin(-53*pi/126) * sin(pi/7) + cos(-53*pi/126) * cos(pi/7),
{
have : cos(-5*pi/18) = cos((-53*pi/126) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/18) = sin(-pi/6) * sin(pi/9) + cos(-pi/6) * cos(pi/9),
{
have : cos(-5*pi/18) = cos((-pi/6) - (pi/9)),
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


lemma Trigo_number_generalization_step2_176 (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) (h2 : ((-sin(pi/12)**2/cos(pi/12)**2+1)*cos(pi/12))≠ 0) (h3 : cos(pi/12)≠ 0) (h4 : (1-(sin(pi/12)/cos(pi/12))**2)≠ 0) : 2*sin(pi/12)/((-sin(pi/12)**2/cos(pi/12)**2 + 1)*cos(pi/12))=sqrt( 3 ) / 3:=
begin
have : 2 * (sin(pi / 12) / cos(pi / 12)) / (1 - (sin(pi / 12) / cos(pi / 12)) ** 2) = 2*sin(pi/12)/((-sin(pi/12)**2/cos(pi/12)**2 + 1)*cos(pi/12)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = sin(pi/12) / cos(pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_177 : -sin(2*pi)*cos(352*pi/3) + cos(2*pi)*cos(13*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2 * pi) * -cos(352 * pi / 3) + cos(2 * pi) * cos(13 * pi / 6) = -sin(2*pi)*cos(352*pi/3) + cos(2*pi)*cos(13*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/6) = -cos(352*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/6) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 6) * sin(2 * pi) + cos(13 * pi / 6) * cos(2 * pi) = sin(2*pi)*sin(13*pi/6) + cos(2*pi)*cos(13*pi/6),
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_178 : -2*cos(pi/10)*cos(pi)*cos(3627*pi/5)=- sin(4*pi/5) / 2 + sin(6*pi/5) / 2:=
begin
have : 2 * -cos(3627 * pi / 5) * cos(pi / 10) * cos(pi) = -2*cos(pi/10)*cos(pi)*cos(3627*pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/10) = -cos(3627*pi/5),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/10) (362),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = 2 * sin(pi/10) * cos(pi/10),
{
have : sin(pi/5) = sin(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) * cos(pi) = - sin(4*pi/5) / 2 + sin(6*pi/5) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi) + (pi/5)) = sin(6*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/5)) = sin(4*pi/5),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_179 : -sin(12595*pi/6)=cos(775*pi/3):=
begin
have : cos(5405*pi/3) = -sin(12595*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5405*pi/3) (148),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(5405*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (901),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(775*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (129),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_180 (h0 : tan(19*pi/4)≠ 0) (h1 : cos((19*pi/2)/2)≠ 0) (h2 : ((1-cos(19*pi/2))/sin(19*pi/2))≠ 0) (h3 : sin(19*pi/2)≠ 0) (h4 : (1-cos(19*pi/2))≠ 0) : sin(19*pi/2)/(1 - cos(19*pi/2))=- 1:=
begin
have : 1 / ((1 - cos(19 * pi / 2)) / sin(19 * pi / 2)) = sin(19*pi/2)/(1 - cos(19*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(19*pi/4) = ( 1 - cos(19*pi/2) ) / sin(19*pi/2),
{
have : tan(19*pi/4) = tan((19*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 1 / tan(19*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (5),
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


lemma Trigo_number_generalization_step2_181 : -3*cos(pi/3) + 4*cos(pi/3)**3=-1 + 2*cos(pi/2)**2:=
begin
have : -(1 - cos(pi / 2) ** 2) + cos(pi / 2) ** 2 = -1 + 2*cos(pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) ** 2 = 1 - cos(pi/2) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
have : 4 * cos(pi / 3) ** 3 - 3 * cos(pi / 3) = -3*cos(pi/3) + 4*cos(pi/3)**3,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_182 (h0 : sin(-10*pi/9)≠ 0) (h1 : (2*sin(-10*pi/9))≠ 0) (h2 : (2*sin((-10)*pi/9))≠ 0) : sin(-20*pi/9)/(2*sin(-10*pi/9))=cos(-pi)*cos(-pi/9) + sin(-pi)*sin(2953*pi/9):=
begin
have : sin((-20) * pi / 9) / (2 * sin((-10) * pi / 9)) = sin(-20*pi/9)/(2*sin(-10*pi/9)),
{
field_simp at *,
},
have : cos(-10*pi/9) = sin(-20*pi/9) / ( 2 * sin(-10*pi/9) ),
{
have : sin(-20*pi/9) = sin(2*(-10*pi/9)),
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
have : - -sin(2953 * pi / 9) * sin(-pi) + cos(-pi / 9) * cos(-pi) = cos(-pi)*cos(-pi/9) + sin(-pi)*sin(2953*pi/9),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = -sin(2953*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/9) (164),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-10*pi/9) = - sin(-pi/9) * sin(-pi) + cos(-pi/9) * cos(-pi),
{
have : cos(-10*pi/9) = cos((-pi/9) + (-pi)),
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


lemma Trigo_number_generalization_step2_183 : sin(-pi/4)*sin(33163*pi/18)=sin(-13*pi/36) / 2 + sin(-5*pi/36) / 2:=
begin
have : cos(2321*pi/9) = sin(33163*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2321*pi/9) (792),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = cos(2321*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (129),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * cos(pi/9) = sin(-13*pi/36) / 2 + sin(-5*pi/36) / 2,
{
rw sin_mul_cos,
have : sin((-pi/4) + (pi/9)) = sin(-5*pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/4) - (pi/9)) = sin(-13*pi/36),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_184 : cos(6227*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos(6227 * pi / 6) = cos(6227*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3869*pi/6) = -cos(6227*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3869*pi/6) (196),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -cos(3869*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (322),
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


lemma Trigo_number_generalization_step2_185 (h0 : tan(179*pi/2)≠ 0) : -1/tan(179*pi/2)=0:=
begin
have : -(1 / tan(179 * pi / 2)) = -1/tan(179*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(562*pi) = 1 / tan(179*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (562*pi) (651),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = -tan(562*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (563),
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


lemma Trigo_number_generalization_step2_186 (h0 : cos(-pi/6)≠ 0) (h1 : (2*cos(-pi/6))≠ 0) : sin(-pi/3)=cos(10373*pi/6):=
begin
have : 2 * (sin(-pi / 3) / (2 * cos(-pi / 6))) * cos(-pi / 6) = sin(-pi/3),
{
field_simp at *,
ring,
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
have : sin(-pi/3) = cos(10373*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (864),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_187 : 3*cos(51811*pi/54) - 4*cos(51811*pi/54)**3=- cos(22687*pi/18):=
begin
have : sin(-pi/27) = cos(51811*pi/54),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/27) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(-pi / 27) ** 3 + 3 * sin(-pi / 27) = 3*sin(-pi/27) - 4*sin(-pi/27)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = -4 * sin(-pi/27) ** 3 + 3 * sin(-pi/27),
{
have : sin(-pi/9) = sin(3*(-pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = - cos(22687*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/9) (630),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_188 : sin(19*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(4184*pi/3) = sin(19*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4184*pi/3) (700),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(4184*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (697),
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


lemma Trigo_number_generalization_step2_189 (h0 : cos(-2*pi)≠ 0) : sin(-17*pi/8)*cos(-pi/8) - cos(-17*pi/8)*cos(8923*pi/8)=sin(-4*pi) / ( 2 * cos(-2*pi) ):=
begin
have : sin((-17) * pi / 8) * cos(-pi / 8) - cos(8923 * pi / 8) * cos((-17) * pi / 8) = sin(-17*pi/8)*cos(-pi/8) - cos(-17*pi/8)*cos(8923*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = cos(8923*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (557),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-17) * pi / 8) * cos(-pi / 8) - sin(-pi / 8) * cos((-17) * pi / 8) = sin(-17*pi/8)*cos(-pi/8) - sin(-pi/8)*cos(-17*pi/8),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-17*pi/8) * cos(-pi/8) - sin(-pi/8) * cos(-17*pi/8),
{
have : sin(-2*pi) = sin((-17*pi/8) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
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


lemma Trigo_number_generalization_step2_190 (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) (h2 : cos(19*pi/84)≠ 0) (h3 : cos(pi/7)≠ 0) (h4 : (1+tan(19*pi/84)*tan(pi/7))≠ 0) (h5 : (tan(pi/7)*tan(19*pi/84)+1)≠ 0) (h6 : ((-(-tan(pi/7)+tan(19*pi/84))**2/(tan(pi/7)*tan(19*pi/84)+1)**2+1)*(tan(pi/7)*tan(19*pi/84)+1))≠ 0) (h7 : (1-((tan(19*pi/84)-tan(pi/7))/(1+tan(19*pi/84)*tan(pi/7)))**2)≠ 0) : 2*(-tan(pi/7) + tan(19*pi/84))/((-(-tan(pi/7) + tan(19*pi/84))**2/(tan(pi/7)*tan(19*pi/84) + 1)**2 + 1)*(tan(pi/7)*tan(19*pi/84) + 1))=sin(pi/6) / cos(pi/6):=
begin
have : 2 * ((tan(19 * pi / 84) - tan(pi / 7)) / (1 + tan(19 * pi / 84) * tan(pi / 7))) / (1 - ((tan(19 * pi / 84) - tan(pi / 7)) / (1 + tan(19 * pi / 84) * tan(pi / 7))) ** 2) = 2*(-tan(pi/7) + tan(19*pi/84))/((-(-tan(pi/7) + tan(19*pi/84))**2/(tan(pi/7)*tan(19*pi/84) + 1)**2 + 1)*(tan(pi/7)*tan(19*pi/84) + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(19*pi/84) - tan(pi/7) ) / ( 1 + tan(19*pi/84) * tan(pi/7) ),
{
have : tan(pi/12) = tan((19*pi/84) - (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_191 : cos(pi/3)/2 + 1/2=1 - sin(10409*pi/6)**2:=
begin
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
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(10409*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (867),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) ** 2 = 1 - sin(pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_192 (h0 : cos(pi/4)≠ 0) (h1 : (2*cos(pi/4))≠ 0) (h2 : (2*cos(2039*pi/4))≠ 0) : sin(pi/2)/(2*cos(2039*pi/4))=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = cos(2039*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/4) (255),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(pi/2) / ( 2 * cos(pi/4) ),
{
have : sin(pi/2) = sin(2*(pi/4)),
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
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_193 : sin(5174*pi/9)**2 + sin(28807*pi/18)**2=1:=
begin
have : (-sin(5174 * pi / 9)) ** 2 + sin(28807 * pi / 18) ** 2 = sin(5174*pi/9)**2 + sin(28807*pi/18)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = -sin(5174*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (287),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = sin(28807*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (800),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) ** 2 + cos(-pi/9) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_194 : -cos(-1808*pi/3)=2 * cos(pi/6) ** 2 - 1:=
begin
have : -cos((-1808) * pi / 3) = -cos(-1808*pi/3),
{
field_simp at *,
},
have : cos(3419*pi/3) = -cos(-1808*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3419*pi/3) (268),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(3419*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (570),
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


lemma Trigo_number_generalization_step2_195 : cos(2551*pi/2)=0:=
begin
have : sin(1020*pi) = cos(2551*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1020*pi) (127),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(1020*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (510),
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


lemma Trigo_number_generalization_step2_196 : sin(pi/5)*sin(pi/4) + cos(pi/5)*cos(5807*pi/4)=- sin(-pi/4) * sin(pi/5) + cos(-pi/4) * cos(pi/5):=
begin
have : cos(pi/4) = cos(5807*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/4) (726),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/20) = sin(pi/5) * sin(pi/4) + cos(pi/5) * cos(pi/4),
{
have : cos(-pi/20) = cos((pi/5) - (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/20) = - sin(-pi/4) * sin(pi/5) + cos(-pi/4) * cos(pi/5),
{
have : cos(-pi/20) = cos((-pi/4) + (pi/5)),
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


lemma Trigo_number_generalization_step2_197 : 1 - 2*cos(4287*pi/5)**2=sin(18623*pi/10):=
begin
have : 1 - 2 * (-cos(4287 * pi / 5)) ** 2 = 1 - 2*cos(4287*pi/5)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/10) = -cos(4287*pi/5),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/10) (428),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = 1 - 2 * sin(pi/10) ** 2,
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = sin(18623*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (931),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_198 (h0 : tan(1019*pi/3)≠ 0) (h1 : cos((2038*pi/3)/2)≠ 0) (h2 : (1+cos(2038*pi/3))≠ 0) (h3 : (sin(2038*pi/3)/(1+cos(2038*pi/3)))≠ 0) (h4 : sin(2038*pi/3)≠ 0) : -(cos(2038*pi/3) + 1)/sin(2038*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / (sin(2038 * pi / 3) / (1 + cos(2038 * pi / 3))) = -(cos(2038*pi/3) + 1)/sin(2038*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(1019*pi/3) = sin(2038*pi/3) / ( 1 + cos(2038*pi/3) ),
{
have : tan(1019*pi/3) = tan((2038*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(1019 * pi / 3) = -1/tan(1019*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1019*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (339),
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


lemma Trigo_number_generalization_step2_199 : sin(-4917*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -sin((-4917) * pi / 4) = sin(-4917*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(7413*pi/4) = -sin(-4917*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (7413*pi/4) (312),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -sin(7413*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (926),
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


lemma Trigo_number_generalization_step2_200 : sin(-pi/9) ** 2=1 - (-1 + 2*(-3*cos(-pi/54) + 4*cos(-pi/54)**3)**2)**2:=
begin
have : 1 - (-1 + 2 * (4 * cos(-pi / 54) ** 3 - 3 * cos(-pi / 54)) ** 2) ** 2 = 1 - (-1 + 2*(-3*cos(-pi/54) + 4*cos(-pi/54)**3)**2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/18) = 4 * cos(-pi/54) ** 3 - 3 * cos(-pi/54),
{
have : cos(-pi/18) = cos(3*(-pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : 1 - (2 * cos(-pi / 18) ** 2 - 1) ** 2 = 1 - (-1 + 2*cos(-pi/18)**2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = 2 * cos(-pi/18) ** 2 - 1,
{
have : cos(-pi/9) = cos(2*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) ** 2 = 1 - cos(-pi/9) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_201 : 3*cos(3508*pi/3) - 4*cos(3508*pi/3)**3=- cos(652*pi):=
begin
have : (-3) * -cos(3508 * pi / 3) + 4 * (-cos(3508 * pi / 3)) ** 3 = 3*cos(3508*pi/3) - 4*cos(3508*pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(3508*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (584),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(-pi) = - cos(652*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (326),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_202 : sin(5045*pi/2)=1:=
begin
have : cos(886*pi) = sin(5045*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (886*pi) (818),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(886*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (443),
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


lemma Trigo_number_generalization_step2_203 : -tan(-173*pi/2)=- tan(1135*pi/2):=
begin
have : -tan((-173) * pi / 2) = -tan(-173*pi/2),
{
field_simp at *,
},
have : tan(505*pi/2) = -tan(-173*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (505*pi/2) (166),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = tan(505*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (252),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - tan(1135*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/2) (568),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_204 : -sin(-pi/6)*cos(pi/5)=sin(-pi/30) / 2 + sin(11*pi/30) / 2:=
begin
have : (-1) / 2 * (2 * sin(-pi / 6) * cos(pi / 5)) = -sin(-pi/6)*cos(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/30) - sin(11*pi/30) = 2 * sin(-pi/6) * cos(pi/5),
{
rw sin_sub_sin,
have : cos(((pi/30) + (11*pi/30))/2) = cos(pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/30) - (11*pi/30))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -1/2*(sin(pi/30) - sin(11*pi/30)) = -sin(pi/30)/2+sin(11*pi/30)/2,
{
ring,
},
conv {to_lhs, rw this,},
have : sin(pi/6) * cos(pi/5) = -sin(pi/30) / 2 + sin(11*pi/30) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/5) + (pi/6)) = sin(11*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (pi/6)) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/6) * cos(pi/5)) = sin(pi/6)*cos(pi/5),
{
ring,
},
have : sin(pi/6) * cos(pi/5) = sin(-pi/30) / 2 + sin(11*pi/30) / 2,
{
rw sin_mul_cos,
have : sin((pi/6) + (pi/5)) = sin(11*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (pi/5)) = sin(-pi/30),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_205 : -sin(7255*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(1453*pi/4) = sin(7255*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (1453*pi/4) (725),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = -cos(1453*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (181),
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


lemma Trigo_number_generalization_step2_206 : sin(-pi) + sin(pi/8)=(-2 + 4*(-sin(-41*pi/32)*sin(pi) + cos(-41*pi/32)*cos(pi))**2)*sin(-7*pi/16):=
begin
have : 2 * (-1 + 2 * (-sin((-41) * pi / 32) * sin(pi) + cos((-41) * pi / 32) * cos(pi)) ** 2) * sin((-7) * pi / 16) = (-2 + 4*(-sin(-41*pi/32)*sin(pi) + cos(-41*pi/32)*cos(pi))**2)*sin(-7*pi/16),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-9*pi/32) = -sin(-41*pi/32) * sin(pi) + cos(-41*pi/32) * cos(pi),
{
have : cos(-9*pi/32) = cos((-41*pi/32) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin((-7) * pi / 16) * (2 * cos((-9) * pi / 32) ** 2 - 1) = 2*(-1 + 2*cos(-9*pi/32)**2)*sin(-7*pi/16),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-9*pi/16) = 2 * cos(-9*pi/32) ** 2 - 1,
{
have : cos(-9*pi/16) = cos(2*(-9*pi/32)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) + sin(pi/8) = 2 * sin(-7*pi/16) * cos(-9*pi/16),
{
rw sin_add_sin,
have : sin(((-pi) + (pi/8))/2) = sin(-7*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (pi/8))/2) = cos(-9*pi/16),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_207 : -4*sin(6443*pi/36)**3 + 3*sin(6443*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-4) * sin(6443 * pi / 36) ** 3 + 3 * sin(6443 * pi / 36) = -4*sin(6443*pi/36)**3 + 3*sin(6443*pi/36),
{
field_simp at *,
},
have : sin(6443*pi/12) = -4 * sin(6443*pi/36) ** 3 + 3 * sin(6443*pi/36),
{
have : sin(6443*pi/12) = sin(3*(6443*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(6443*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (268),
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


lemma Trigo_number_generalization_step2_208 : -sin(1774*pi/3)=- cos(3653*pi/6):=
begin
have : cos(8269*pi/6) = -sin(1774*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8269*pi/6) (984),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(8269*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (689),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(3653*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (304),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_209 : 1 - 2*sin(581*pi/2)**2=- cos(70*pi):=
begin
have : 1 - 2 * (-sin(581 * pi / 2)) ** 2 = 1 - 2*sin(581*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -sin(581*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (145),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(-pi) = - cos(70*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_210 : sin(-7*pi/12)*sin(5947*pi/4) - sin(-pi/4)*cos(-7*pi/12)=- sin(2977*pi/3):=
begin
have : sin((-7) * pi / 12) * sin(5947 * pi / 4) - sin(-pi / 4) * cos((-7) * pi / 12) = sin(-7*pi/12)*sin(5947*pi/4) - sin(-pi/4)*cos(-7*pi/12),
{
field_simp at *,
},
have : cos(-pi/4) = sin(5947*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-7) * pi / 12) * cos(-pi / 4) - sin(-pi / 4) * cos((-7) * pi / 12) = sin(-7*pi/12)*cos(-pi/4) - sin(-pi/4)*cos(-7*pi/12),
{
field_simp at *,
},
have : sin(-pi/3) = sin(-7*pi/12) * cos(-pi/4) - sin(-pi/4) * cos(-7*pi/12),
{
have : sin(-pi/3) = sin((-7*pi/12) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(2977*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (496),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_211 : sin(2045*pi/2)=sin(257*pi/2):=
begin
have : sin(pi/2) = sin(2045*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (511),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(257 * pi / 2) = sin(257*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(1725*pi) = -sin(257*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1725*pi) (926),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = - cos(1725*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (862),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_212 : sin(4325*pi/3)=- sqrt( 3 ) / 2:=
begin
have : - -sin(4325 * pi / 3) = sin(4325*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(4040*pi/3) = -sin(4325*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4040*pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(4040*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (673),
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


lemma Trigo_number_generalization_step2_213 (h0 : cos(2*pi/3)≠ 0) (h1 : (2*cos(2*pi/3))≠ 0) : cos(3869*pi/6)/(2*cos(2*pi/3))=sqrt( 3 ) / 2:=
begin
have : sin(4*pi/3) = cos(3869*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/3) (321),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(4*pi/3) / ( 2 * cos(2*pi/3) ),
{
have : sin(4*pi/3) = sin(2*(2*pi/3)),
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
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_214 : -sin(-pi/6)*cos(5*pi/6) - sin(-pi)/2 + sin(2*pi/3)/2=2 * sin(pi/2) * cos(pi/2):=
begin
have : -sin(-pi / 6) * cos(5 * pi / 6) + (-sin(-pi) / 2 + sin(2 * pi / 3) / 2) = -sin(-pi/6)*cos(5*pi/6) - sin(-pi)/2 + sin(2*pi/3)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) * cos(-pi/6) = -sin(-pi) / 2 + sin(2*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/6) + (5*pi/6)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (5*pi/6)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(5*pi/6) * cos(-pi/6)) = sin(5*pi/6)*cos(-pi/6),
{
ring,
},
have : sin(5 * pi / 6) * cos(-pi / 6) - sin(-pi / 6) * cos(5 * pi / 6) = -sin(-pi/6)*cos(5*pi/6) + sin(5*pi/6)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(5*pi/6) * cos(-pi/6) - sin(-pi/6) * cos(5*pi/6),
{
have : sin(pi) = sin((5*pi/6) - (-pi/6)),
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


lemma Trigo_number_generalization_step2_215 : -cos(2*pi)*cos(1791*pi/2) - sin(2*pi)*sin(1791*pi/2)=0:=
begin
have : -(sin(1791 * pi / 2) * sin(2 * pi) + cos(1791 * pi / 2) * cos(2 * pi)) = -cos(2*pi)*cos(1791*pi/2) - sin(2*pi)*sin(1791*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1787*pi/2) = sin(1791*pi/2) * sin(2*pi) + cos(1791*pi/2) * cos(2*pi),
{
have : cos(1787*pi/2) = cos((1791*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(1787*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (446),
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


lemma Trigo_number_generalization_step2_216 : sin(8726*pi/3)=sin(656*pi/3):=
begin
have : - -sin(8726 * pi / 3) = sin(8726*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(11143*pi/6) = -sin(8726*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (11143*pi/6) (525),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(11143*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (928),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(656*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (109),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_217 : cos(1621*pi/3)=1 / 2:=
begin
have : sin(3817*pi/6) = cos(1621*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3817*pi/6) (588),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(3817*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (318),
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


lemma Trigo_number_generalization_step2_218 (h0 : sin(-pi/4)≠ 0) (h1 : (2*sin(-pi/4))≠ 0) : sin(-pi/2)/(2*sin(-pi/4))=sin(8611*pi/4):=
begin
have : - -sin(8611 * pi / 4) = sin(8611*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(6741*pi/4) = -sin(8611*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (6741*pi/4) (233),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = sin(-pi/2) / ( 2 * sin(-pi/4) ),
{
have : sin(-pi/2) = sin(2*(-pi/4)),
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
have : cos(-pi/4) = - cos(6741*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (842),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_219 : -cos(2318*pi/3)=-1 + 2*cos(pi/6)**2:=
begin
have : cos(pi/3) = -cos(2318*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (386),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - cos(pi / 6) ** 2) + cos(pi / 6) ** 2 = -1 + 2*cos(pi/6)**2,
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


lemma Trigo_number_generalization_step2_220 : cos(9129*pi/5)=sin(-pi/5)*cos(-pi/2) + cos(-pi/5)*cos(1310*pi):=
begin
have : sin(-pi / 5) * cos(-pi / 2) - -cos(1310 * pi) * cos(-pi / 5) = sin(-pi/5)*cos(-pi/2) + cos(-pi/5)*cos(1310*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -cos(1310*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (655),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi/10) = cos(9129*pi/5),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/10) (912),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/10) = sin(-pi/5) * cos(-pi/2) - sin(-pi/2) * cos(-pi/5),
{
have : sin(3*pi/10) = sin((-pi/5) - (-pi/2)),
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


lemma Trigo_number_generalization_step2_221 (h0 : tan(3891*pi/4)≠ 0) (h1 : ((-1)/tan(4393*pi/4))≠ 0) (h2 : tan(4393*pi/4)≠ 0) : -tan(4393*pi/4)=- 1:=
begin
have : 1 / ((-1) / tan(4393 * pi / 4)) = -tan(4393*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3891*pi/4) = -1 / tan(4393*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (3891*pi/4) (125),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 1 / tan(3891*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (973),
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


lemma Trigo_number_generalization_step2_222 : sin(1815*pi)=sin(pi)*cos(-pi) - sin(-pi)*cos(103*pi):=
begin
have : cos(pi) = cos(103*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = sin(1815*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (908),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(pi) * cos(-pi) - sin(-pi) * cos(pi),
{
have : sin(2*pi) = sin((pi) - (-pi)),
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


lemma Trigo_number_generalization_step2_223 : cos(1612*pi)=-1 + 2*cos(-pi)**2:=
begin
have : cos(-2*pi) = cos(1612*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (805),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (1 - cos(-pi) ** 2) = -1 + 2*cos(-pi)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) ** 2 = 1 - cos(-pi) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step2_224 (h0 : cos(9311*pi/6)≠ 0) (h1 : (2*cos(9311*pi/6))≠ 0) : -sin(9311*pi/3)/(2*cos(9311*pi/6))=1 / 2:=
begin
have : -(sin(9311 * pi / 3) / (2 * cos(9311 * pi / 6))) = -sin(9311*pi/3)/(2*cos(9311*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(9311*pi/6) = sin(9311*pi/3) / ( 2 * cos(9311*pi/6) ),
{
have : sin(9311*pi/3) = sin(2*(9311*pi/6)),
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
have : cos(pi/3) = -sin(9311*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (775),
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


lemma Trigo_number_generalization_step2_225 : -cos(568*pi/3)=1 / 2:=
begin
have : cos(4994*pi/3) = cos(568*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (4994*pi/3) (927),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(4994*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (832),
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


lemma Trigo_number_generalization_step2_226 : cos(4337*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(2351*pi/4) = cos(4337*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2351*pi/4) (836),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(2351*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (293),
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


lemma Trigo_number_generalization_step2_227 : (sin(27583*pi/15)*cos(-pi/5) + sin(-pi/5)*cos(27583*pi/15))**2=1 - cos(pi/3) ** 2:=
begin
have : sin(5516*pi/3) = sin(27583*pi/15) * cos(-pi/5) + sin(-pi/5) * cos(27583*pi/15),
{
have : sin(5516*pi/3) = sin((27583*pi/15) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(5516*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (919),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 = 1 - cos(pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_228 : -sin(pi/2)*cos(3505*pi/3) + sin(pi/3)*cos(pi/2)=- sin(1493*pi/6):=
begin
have : cos(pi/3) = cos(3505*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (584),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(pi / 3) = -sin(pi/2)*cos(pi/3) + sin(pi/3)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(1493*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (124),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_229 : -sin(6419*pi/18)*cos(pi/9) + sin(pi/9)*cos(6419*pi/18)=- 1:=
begin
have : -(sin(6419 * pi / 18) * cos(pi / 9) - sin(pi / 9) * cos(6419 * pi / 18)) = -sin(6419*pi/18)*cos(pi/9) + sin(pi/9)*cos(6419*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(713*pi/2) = sin(6419*pi/18) * cos(pi/9) - sin(pi/9) * cos(6419*pi/18),
{
have : sin(713*pi/2) = sin((6419*pi/18) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(713*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (178),
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


lemma Trigo_number_generalization_step2_230 : 1 - 2*sin(2759*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : cos(2759*pi/6) = 1 - 2 * sin(2759*pi/12) ** 2,
{
have : cos(2759*pi/6) = cos(2*(2759*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(2759*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (230),
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


lemma Trigo_number_generalization_step2_231 : -sin(-2695*pi/3)=- sin(647*pi/3):=
begin
have : -sin((-2695) * pi / 3) = -sin(-2695*pi/3),
{
field_simp at *,
},
have : sin(5797*pi/3) = -sin(-2695*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5797*pi/3) (517),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(5797*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (966),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(647*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (108),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_232 : sin(-pi/4)*cos(-pi/12) - sin(-pi/12)*sin(7999*pi/4)=- cos(11051*pi/6):=
begin
have : sin(-pi / 4) * cos(-pi / 12) + sin(-pi / 12) * -sin(7999 * pi / 4) = sin(-pi/4)*cos(-pi/12) - sin(-pi/12)*sin(7999*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -sin(7999*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 12) * cos(-pi / 4) + sin(-pi / 4) * cos(-pi / 12) = sin(-pi/4)*cos(-pi/12) + sin(-pi/12)*cos(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-pi/12) * cos(-pi/4) + sin(-pi/4) * cos(-pi/12),
{
have : sin(-pi/3) = sin((-pi/12) + (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - cos(11051*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (920),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_233 (h0 : tan(199*pi/6)≠ 0) (h1 : (sin(199*pi/6)/cos(199*pi/6))≠ 0) (h2 : sin(199*pi/6)≠ 0) (h3 : cos(199*pi/6)≠ 0) : cos(199*pi/6)/sin(199*pi/6)=sqrt( 3 ):=
begin
have : 1 / (sin(199 * pi / 6) / cos(199 * pi / 6)) = cos(199*pi/6)/sin(199*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(199*pi/6) = sin(199*pi/6) / cos(199*pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(199*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (33),
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


lemma Trigo_number_generalization_step2_234 : 1 - 2*sin(-pi)**2=cos(1050*pi):=
begin
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
have : sin(301*pi/2) = cos(1050*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (301*pi/2) (449),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(301*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_235 (h0 : cos((-pi/4)/2)≠ 0) (h1 : (cos(-pi/4)+1)≠ 0) (h2 : (1+cos(-pi/4))≠ 0) : sin(2301*pi/4)/(cos(-pi/4) + 1)=tan(4399*pi/8):=
begin
have : sin(-pi/4) = sin(2301*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/4) (287),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 4) / (1 + cos(-pi / 4)) = sin(-pi/4)/(cos(-pi/4) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = sin(-pi/4) / ( 1 + cos(-pi/4) ),
{
have : tan(-pi/8) = tan((-pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = tan(4399*pi/8),
{
rw tan_eq_tan_add_int_mul_pi (-pi/8) (550),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_236 : cos(4927*pi/3)=1 / 2:=
begin
have : - -cos(4927 * pi / 3) = cos(4927*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1084*pi/3) = -cos(4927*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (1084*pi/3) (640),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(1084*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (180),
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


lemma Trigo_number_generalization_step2_237 : -2*sin(3459*pi/2)*cos(pi/2)=sin(252*pi):=
begin
have : 2 * -sin(3459 * pi / 2) * cos(pi / 2) = -2*sin(3459*pi/2)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(3459*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (865),
focus{repeat {apply congr_arg _}},
simp,
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
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(252*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (126),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_238 : cos(15107*pi/6)=- sin(2716*pi/3):=
begin
have : - -cos(15107 * pi / 6) = cos(15107*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2458*pi/3) = -cos(15107*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2458*pi/3) (849),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(2458*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (409),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(2716*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (452),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_239 : -cos(1389*pi/2) + sin(-2*pi)=-sin(-pi) + sin(-2*pi):=
begin
have : 2 * (-sin(-pi) / 2 + sin((-2) * pi) / 2) = -sin(-pi) + sin(-2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) * cos(-3*pi/2) = -sin(-pi) / 2 + sin(-2*pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-3*pi/2) + (-pi/2)) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-3*pi/2) - (-pi/2)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-pi/2) * cos(-3*pi/2)) = 2*sin(-pi/2)*cos(-3*pi/2),
{
ring,
},
conv {to_rhs, rw this,},
have : sin((-2) * pi) - cos(1389 * pi / 2) = -cos(1389*pi/2) + sin(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(1389*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (347),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) - sin(-pi) = 2 * sin(-pi/2) * cos(-3*pi/2),
{
rw sin_sub_sin,
have : cos(((-2*pi) + (-pi))/2) = cos(-3*pi/2),
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
},
rw this,
end


lemma Trigo_number_generalization_step2_240 : -cos(-30*pi)=- 1:=
begin
have : -cos((-30) * pi) = -cos(-30*pi),
{
field_simp at *,
},
have : sin(3433*pi/2) = cos(-30*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3433*pi/2) (843),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(3433*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (857),
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


lemma Trigo_number_generalization_step2_241 (h0 : sin(2521*pi/4)≠ 0) (h1 : (4*sin(2521*pi/4)**2)≠ 0) (h2 : (2*sin(2521*pi/4))≠ 0) : sin(2521*pi/2)**2/(4*sin(2521*pi/4)**2)=1 - sin(pi/4) ** 2:=
begin
have : (sin(2521 * pi / 2) / (2 * sin(2521 * pi / 4))) ** 2 = sin(2521*pi/2)**2/(4*sin(2521*pi/4)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2521*pi/4) = sin(2521*pi/2) / ( 2 * sin(2521*pi/4) ),
{
have : sin(2521*pi/2) = sin(2*(2521*pi/4)),
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
have : cos(pi/4) = cos(2521*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (315),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) ** 2 = 1 - sin(pi/4) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_242 (h0 : cos(5963*pi/12)≠ 0) (h1 : (1-tan(5963*pi/12)**2)≠ 0) : -2*tan(5963*pi/12)/(1 - tan(5963*pi/12)**2)=sqrt( 3 ) / 3:=
begin
have : -(2 * tan(5963 * pi / 12) / (1 - tan(5963 * pi / 12) ** 2)) = -2*tan(5963*pi/12)/(1 - tan(5963*pi/12)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(5963*pi/6) = 2 * tan(5963*pi/12) / ( 1 - tan(5963*pi/12) ** 2 ),
{
have : tan(5963*pi/6) = tan(2*(5963*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(5963*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (994),
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


lemma Trigo_number_generalization_step2_243 (h0 : tan(1652*pi/3)≠ 0) (h1 : tan(4133*pi/3)≠ 0) : -1/tan(4133*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(4133 * pi / 3) = -1/tan(4133*pi/3),
{
field_simp at *,
},
have : tan(1652*pi/3) = tan(4133*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (1652*pi/3) (827),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(1652 * pi / 3) = -1/tan(1652*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1652*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (550),
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


lemma Trigo_number_generalization_step2_244 : -32*sin(pi/12)**3*cos(pi/12)**3 + 6*sin(pi/12)*cos(pi/12)=1:=
begin
have : (-4) * (2 * sin(pi / 12) * cos(pi / 12)) ** 3 + 3 * (2 * sin(pi / 12) * cos(pi / 12)) = -32*sin(pi/12)**3*cos(pi/12)**3 + 6*sin(pi/12)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 6) ** 3 + 3 * sin(pi / 6) = -4*sin(pi/6)**3 + 3*sin(pi/6),
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_245 (h0 : cos(-pi/7)≠ 0) (h1 : (2*cos(-pi/7))≠ 0) (h2 : (4*cos(-pi/7)**2)≠ 0) (h3 : (4*sin(3757*pi/14)**2)≠ 0) : sin(-2*pi/7)**2/(4*sin(3757*pi/14)**2)=1 - cos(-pi/7) ** 2:=
begin
have : sin((-2) * pi / 7) ** 2 / (4 * sin(3757 * pi / 14) ** 2) = sin(-2*pi/7)**2/(4*sin(3757*pi/14)**2),
{
field_simp at *,
},
have : cos(-pi/7) = sin(3757*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/7) (134),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-2) * pi / 7) / (2 * cos(-pi / 7))) ** 2 = sin(-2*pi/7)**2/(4*cos(-pi/7)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = sin(-2*pi/7) / ( 2 * cos(-pi/7) ),
{
have : sin(-2*pi/7) = sin(2*(-pi/7)),
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
have : sin(-pi/7) ** 2 = 1 - cos(-pi/7) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_246 : -cos(8173*pi/6)**2 + cos(pi/3)**2=- 1 / 2:=
begin
have : sin(pi/3) = cos(8173*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (681),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(pi/3) ** 2 + cos(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_247 (h0 : sin(pi/9)≠ 0) (h1 : (2*sin(pi/9)**3)≠ 0) (h2 : (2*sin(pi/9))≠ 0) : -3*sin(2*pi/9)/(2*sin(pi/9)) + sin(2*pi/9)**3/(2*sin(pi/9)**3)=- cos(2222*pi/3):=
begin
have : (-3) * (sin(2 * pi / 9) / (2 * sin(pi / 9))) + 4 * (sin(2 * pi / 9) / (2 * sin(pi / 9))) ** 3 = -3*sin(2*pi/9)/(2*sin(pi/9)) + sin(2*pi/9)**3/(2*sin(pi/9)**3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = sin(2*pi/9) / ( 2 * sin(pi/9) ),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
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
have : cos(pi/3) = - cos(2222*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (370),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_248 : -sin(-pi/2)*cos(1235*pi/4) + sin(1235*pi/4)*cos(-pi/2)=- sqrt( 2 ) / 2:=
begin
have : sin(1235 * pi / 4) * cos(-pi / 2) - sin(-pi / 2) * cos(1235 * pi / 4) = -sin(-pi/2)*cos(1235*pi/4) + sin(1235*pi/4)*cos(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1237*pi/4) = sin(1235*pi/4) * cos(-pi/2) - sin(-pi/2) * cos(1235*pi/4),
{
have : sin(1237*pi/4) = sin((1235*pi/4) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = sin(1237*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (154),
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


lemma Trigo_number_generalization_step2_249 : -sin(2893*pi/8)**2 + cos(3*pi/8)**2=- sqrt( 2 ) / 2:=
begin
have : -(-sin(2893 * pi / 8)) ** 2 + cos(3 * pi / 8) ** 2 = -sin(2893*pi/8)**2 + cos(3*pi/8)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/8) = -sin(2893*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (3*pi/8) (181),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(3*pi/8) ** 2 + cos(3*pi/8) ** 2,
{
have : cos(3*pi/4) = cos(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_250 : cos(-6299*pi/7)=- cos(1714*pi/7):=
begin
have : - -cos((-6299) * pi / 7) = cos(-6299*pi/7),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(16483*pi/14) = -cos(-6299*pi/7),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (16483*pi/14) (138),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = -sin(16483*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (588),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = - cos(1714*pi/7),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/7) (122),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_251 : -cos(3861*pi/10)=-2*sin(-pi/5)*cos(4464*pi/5):=
begin
have : sin(-2*pi/5) = -cos(3861*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi/5) (193),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 5) * -cos(4464 * pi / 5) = -2*sin(-pi/5)*cos(4464*pi/5),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) = -cos(4464*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/5) (446),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/5) = 2 * sin(-pi/5) * cos(-pi/5),
{
have : sin(-2*pi/5) = sin(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_252 : (-sin(-pi/7)*cos(2441*pi/63) + sin(2441*pi/63)*cos(-pi/7))*cos(-pi)=- sin(-10*pi/9) / 2 + sin(-8*pi/9) / 2:=
begin
have : (sin(2441 * pi / 63) * cos(-pi / 7) - sin(-pi / 7) * cos(2441 * pi / 63)) * cos(-pi) = (-sin(-pi/7)*cos(2441*pi/63) + sin(2441*pi/63)*cos(-pi/7))*cos(-pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(350*pi/9) = sin(2441*pi/63) * cos(-pi/7) - sin(-pi/7) * cos(2441*pi/63),
{
have : sin(350*pi/9) = sin((2441*pi/63) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(350*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) * cos(-pi) = - sin(-10*pi/9) / 2 + sin(-8*pi/9) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi) + (pi/9)) = sin(-8*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (pi/9)) = sin(-10*pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_253 (h0 : tan(3439*pi/6)≠ 0) (h1 : cos((3439*pi/3)/2)≠ 0) (h2 : (1+cos(3439*pi/3))≠ 0) (h3 : sin(3439*pi/3)≠ 0) (h4 : (sin(3439*pi/3)/(1+cos(3439*pi/3)))≠ 0) : (cos(3439*pi/3) + 1)/sin(3439*pi/3)=sqrt( 3 ):=
begin
have : 1 / (sin(3439 * pi / 3) / (1 + cos(3439 * pi / 3))) = (cos(3439*pi/3) + 1)/sin(3439*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3439*pi/6) = sin(3439*pi/3) / ( 1 + cos(3439*pi/3) ),
{
have : tan(3439*pi/6) = tan((3439*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(3439*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (573),
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


lemma Trigo_number_generalization_step2_254 : 2*sin(12871*pi/12)*cos(5*pi/12)=1 / 2:=
begin
have : sin(5*pi/12) = sin(12871*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/12) (536),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 2 * sin(5*pi/12) * cos(5*pi/12),
{
have : sin(5*pi/6) = sin(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_255 : -cos(18727*pi/9)=2 * cos(-pi/9) ** 2 - 1:=
begin
have : cos(8710*pi/9) = -cos(18727*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (8710*pi/9) (556),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/9) = cos(8710*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi/9) (484),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/9) = 2 * cos(-pi/9) ** 2 - 1,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_256 : cos(2*pi/7)=-8*sin(1999*pi/7)**2*cos(1999*pi/7)**2 + 1:=
begin
have : 1 - 2 * (2 * sin(1999 * pi / 7) * cos(1999 * pi / 7)) ** 2 = -8*sin(1999*pi/7)**2*cos(1999*pi/7)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3998*pi/7) = 2 * sin(1999*pi/7) * cos(1999*pi/7),
{
have : sin(3998*pi/7) = sin(2*(1999*pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : 1 - 2 * (-sin(3998 * pi / 7)) ** 2 = 1 - 2*sin(3998*pi/7)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = -sin(3998*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/7) (285),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/7) = 1 - 2 * sin(pi/7) ** 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_257 : (1 - 2*sin(-pi/4)**2)*sin(0) - sin(-pi/2)*cos(0)=1:=
begin
have : sin(0) * (1 - 2 * sin(-pi / 4) ** 2) - sin(-pi / 2) * cos(0) = (1 - 2*sin(-pi/4)**2)*sin(0) - sin(-pi/2)*cos(0),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/2) = sin(0) * cos(-pi/2) - sin(-pi/2) * cos(0),
{
have : sin(pi/2) = sin((0) - (-pi/2)),
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


lemma Trigo_number_generalization_step2_258 : 2*sin(2547*pi/4)*cos(pi/4)=1:=
begin
have : sin(pi/4) = sin(2547*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (318),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_259 (h0 : cos(1509*pi)≠ 0) (h1 : (2*cos(1509*pi))≠ 0) : -sin(3018*pi)/(2*cos(1509*pi))=0:=
begin
have : -(sin(3018 * pi) / (2 * cos(1509 * pi))) = -sin(3018*pi)/(2*cos(1509*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1509*pi) = sin(3018*pi) / ( 2 * cos(1509*pi) ),
{
have : sin(3018*pi) = sin(2*(1509*pi)),
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
have : cos(pi/2) = -sin(1509*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (754),
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


lemma Trigo_number_generalization_step2_260 (h0 : cos(8353*pi/6)≠ 0) (h1 : (2*cos(8353*pi/6))≠ 0) : sin(8353*pi/3)/(2*cos(8353*pi/6))=1 / 2:=
begin
have : sin(8353*pi/6) = sin(8353*pi/3) / ( 2 * cos(8353*pi/6) ),
{
have : sin(8353*pi/3) = sin(2*(8353*pi/6)),
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
have : sin(5*pi/6) = sin(8353*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (696),
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


lemma Trigo_number_generalization_step2_261 (h0 : -cos(7370*pi/9)≠ 0) (h1 : cos(7370*pi/9)≠ 0) : -sin(6722*pi/9)/cos(7370*pi/9)=tan(pi/9):=
begin
have : sin(pi/9) = sin(6722*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (373),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 9) / -cos(7370 * pi / 9) = -sin(pi/9)/cos(7370*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -cos(7370*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/9) (409),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) / cos(pi/9) = tan(pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_262 : cos(3965*pi/2) + cos(-pi/8)=-2*sin(-5*pi/16)*cos(20997*pi/16):=
begin
have : (-2) * cos(20997 * pi / 16) * sin((-5) * pi / 16) = -2*sin(-5*pi/16)*cos(20997*pi/16),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi/16) = cos(20997*pi/16),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/16) (656),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi / 8) - -cos(3965 * pi / 2) = cos(3965*pi/2) + cos(-pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -cos(3965*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (991),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) - cos(-pi/2) = - 2 * sin(3*pi/16) * sin(-5*pi/16),
{
rw cos_sub_cos,
have : sin(((-pi/8) + (-pi/2))/2) = sin(-5*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/8) - (-pi/2))/2) = sin(3*pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_263 : -cos(14081*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(1375*pi/3) = -cos(14081*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1375*pi/3) (944),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(1375*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (229),
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


lemma Trigo_number_generalization_step2_264 (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : -sin(pi/6)*sin(pi)/(2*sin(pi/2)) + sin(pi/2)*cos(pi/6)=- cos(391*pi/6):=
begin
have : -sin(pi / 6) * (sin(pi) / (2 * sin(pi / 2))) + sin(pi / 2) * cos(pi / 6) = -sin(pi/6)*sin(pi)/(2*sin(pi/2)) + sin(pi/2)*cos(pi/6),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi / 2) * cos(pi / 6) - sin(pi / 6) * cos(pi / 2) = -sin(pi/6)*cos(pi/2) + sin(pi/2)*cos(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(pi/2) * cos(pi/6) - sin(pi/6) * cos(pi/2),
{
have : sin(pi/3) = sin((pi/2) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - cos(391*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_265 (h0 : tan(4891*pi/6)≠ 0) (h1 : (sin(4891*pi/6)/cos(4891*pi/6))≠ 0) (h2 : cos(4891*pi/6)≠ 0) (h3 : sin(4891*pi/6)≠ 0) : cos(4891*pi/6)/sin(4891*pi/6)=sqrt( 3 ):=
begin
have : 1 / (sin(4891 * pi / 6) / cos(4891 * pi / 6)) = cos(4891*pi/6)/sin(4891*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(4891*pi/6) = sin(4891*pi/6) / cos(4891*pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(4891*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (815),
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


lemma Trigo_number_generalization_step2_266 : 1 - cos(17*pi/6)**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : 1 - (-cos(17 * pi / 6)) ** 2 = 1 - cos(17*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(17*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) ** 2 = 1 - sin(pi/3) ** 2,
{
rw cos_sq',
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


lemma Trigo_number_generalization_step2_267 : -3 + 4*(1 - 2*sin(5*pi/36)**2)**3 + 6*sin(5*pi/36)**2=- sqrt( 3 ) / 2:=
begin
have : (-3) * (1 - 2 * sin(5 * pi / 36) ** 2) + 4 * (1 - 2 * sin(5 * pi / 36) ** 2) ** 3 = -3 + 4*(1 - 2*sin(5*pi/36)**2)**3 + 6*sin(5*pi/36)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/18) = 1 - 2 * sin(5*pi/36) ** 2,
{
have : cos(5*pi/18) = cos(2*(5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : 4 * cos(5 * pi / 18) ** 3 - 3 * cos(5 * pi / 18) = -3*cos(5*pi/18) + 4*cos(5*pi/18)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = 4 * cos(5*pi/18) ** 3 - 3 * cos(5*pi/18),
{
have : cos(5*pi/6) = cos(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_268 : cos(-50*pi)=1:=
begin
have : cos((-50) * pi) = cos(-50*pi),
{
field_simp at *,
},
have : cos(898*pi) = cos(-50*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (898*pi) (424),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(898*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (449),
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


lemma Trigo_number_generalization_step2_269 (h0 : cos(3321*pi/2)≠ 0) (h1 : (2*cos(3321*pi/2))≠ 0) : -1 + 2*cos(pi)**2=sin(3321*pi)/(2*cos(3321*pi/2)):=
begin
have : sin(3321*pi/2) = sin(3321*pi) / ( 2 * cos(3321*pi/2) ),
{
have : sin(3321*pi) = sin(2*(3321*pi/2)),
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
have : cos(2*pi) = sin(3321*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (831),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_270 : -sin(pi/4)**2 + (-3*cos(pi/12) + 4*cos(pi/12)**3)**2=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : -sin(pi / 4) ** 2 + (4 * cos(pi / 12) ** 3 - 3 * cos(pi / 12)) ** 2 = -sin(pi/4)**2 + (-3*cos(pi/12) + 4*cos(pi/12)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_271 : -3*cos(6775*pi/4) + 4*cos(6775*pi/4)**3=- sqrt( 2 ) / 2:=
begin
have : (-3) * cos(6775 * pi / 4) + 4 * cos(6775 * pi / 4) ** 3 = -3*cos(6775*pi/4) + 4*cos(6775*pi/4)**3,
{
field_simp at *,
},
have : cos(pi/4) = cos(6775*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/4) (847),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(pi / 4) ** 3 - 3 * cos(pi / 4) = -3*cos(pi/4) + 4*cos(pi/4)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = 4 * cos(pi/4) ** 3 - 3 * cos(pi/4),
{
have : cos(3*pi/4) = cos(3*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_272 : -sin(5227*pi/14)=sin(pi/9)*cos(191993*pi/126) - sin(191993*pi/126)*cos(pi/9):=
begin
have : cos(pi/7) = -sin(5227*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (186),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(191993 * pi / 126) * cos(pi / 9) - sin(pi / 9) * cos(191993 * pi / 126)) = sin(pi/9)*cos(191993*pi/126) - sin(191993*pi/126)*cos(pi/9),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(21331*pi/14) = sin(191993*pi/126) * cos(pi/9) - sin(pi/9) * cos(191993*pi/126),
{
have : sin(21331*pi/14) = sin((191993*pi/126) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = - sin(21331*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (761),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_273 : -sin(11197*pi/8)=-4*sin(4583*pi/8)**3 + 3*sin(4583*pi/8):=
begin
have : cos(-pi/8) = -sin(11197*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (699),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(4583 * pi / 8) ** 3 + 3 * sin(4583 * pi / 8) = -4*sin(4583*pi/8)**3 + 3*sin(4583*pi/8),
{
field_simp at *,
},
have : sin(13749*pi/8) = -4 * sin(4583*pi/8) ** 3 + 3 * sin(4583*pi/8),
{
have : sin(13749*pi/8) = sin(3*(4583*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = sin(13749*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/8) (859),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_274 : sin(1339*pi/5)=cos(-7*pi/10)/2 - cos(-3*pi/10)/2 + cos(-pi/2)*cos(-pi/5):=
begin
have : cos(-7*pi/10) = sin(1339*pi/5),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-7*pi/10) (134),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(cos((-3) * pi / 10) / 2 - cos((-7) * pi / 10) / 2) + cos(-pi / 2) * cos(-pi / 5) = cos(-7*pi/10)/2 - cos(-3*pi/10)/2 + cos(-pi/2)*cos(-pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) * sin(-pi/5) = cos(-3*pi/10) / 2 - cos(-7*pi/10) / 2,
{
rw sin_mul_sin,
have : cos((-pi/2) + (-pi/5)) = cos(-7*pi/10),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (-pi/5)) = cos(-3*pi/10),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -(sin(-pi/2) * sin(-pi/5)) = -sin(-pi/2)*sin(-pi/5),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-7*pi/10) = - sin(-pi/2) * sin(-pi/5) + cos(-pi/2) * cos(-pi/5),
{
have : cos(-7*pi/10) = cos((-pi/2) + (-pi/5)),
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


lemma Trigo_number_generalization_step2_275 : -sin(pi/3)*cos(3761*pi/14)=sin(20999*pi/42)/2 + cos(4*pi/21)/2:=
begin
have : sin(pi / 3) * -cos(3761 * pi / 14) = -sin(pi/3)*cos(3761*pi/14),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = -cos(3761*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/7) (134),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4 * pi / 21) / 2 - -sin(20999 * pi / 42) / 2 = sin(20999*pi/42)/2 + cos(4*pi/21)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(10*pi/21) = -sin(20999*pi/42),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (10*pi/21) (249),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) * sin(pi/7) = cos(4*pi/21) / 2 - cos(10*pi/21) / 2,
{
rw sin_mul_sin,
have : cos((pi/3) + (pi/7)) = cos(10*pi/21),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (pi/7)) = cos(4*pi/21),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_276 (h0 : (sin(pi/12)*sin(-pi/6)+cos(pi/12)*cos(-pi/6))≠ 0) (h1 : (sin(-pi/6)*sin(pi/12)+cos(-pi/6)*cos(pi/12))≠ 0) (h2 : sin(-pi/6)≠ 0) (h3 : (sin(-pi/6)*sin(pi/12)+sin(-pi/3)*cos(pi/12)/(2*sin(-pi/6)))≠ 0) (h4 : (2*sin(-pi/6))≠ 0) (h5 : (sin(-pi/6)*sin(pi/12)+sin(-pi/3)/(2*sin(-pi/6))*cos(pi/12))≠ 0) : sin(pi/4)/(sin(-pi/6)*sin(pi/12) + sin(-pi/3)*cos(pi/12)/(2*sin(-pi/6)))=tan(pi/4):=
begin
have : sin(pi / 4) / (sin(-pi / 6) * sin(pi / 12) + sin(-pi / 3) / (2 * sin(-pi / 6)) * cos(pi / 12)) = sin(pi/4)/(sin(-pi/6)*sin(pi/12) + sin(-pi/3)*cos(pi/12)/(2*sin(-pi/6))),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi / 4) / (sin(pi / 12) * sin(-pi / 6) + cos(pi / 12) * cos(-pi / 6)) = sin(pi/4)/(sin(-pi/6)*sin(pi/12) + cos(-pi/6)*cos(pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(pi/12) * sin(-pi/6) + cos(pi/12) * cos(-pi/6),
{
have : cos(pi/4) = cos((pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) / cos(pi/4) = tan(pi/4),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_277 : -8*sin(3*pi/16)**2*cos(3*pi/16)**2 + 1=- sqrt( 2 ) / 2:=
begin
have : 1 - 2 * (2 * sin(3 * pi / 16) * cos(3 * pi / 16)) ** 2 = -8*sin(3*pi/16)**2*cos(3*pi/16)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/8) = 2 * sin(3*pi/16) * cos(3*pi/16),
{
have : sin(3*pi/8) = sin(2*(3*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = 1 - 2 * sin(3*pi/8) ** 2,
{
have : cos(3*pi/4) = cos(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_278 : -4*(-4*sin(pi/12)**3 + 3*sin(pi/12))**3 - 12*sin(pi/12)**3 + 9*sin(pi/12)=sqrt( 2 ) / 2:=
begin
have : (-4) * ((-4) * sin(pi / 12) ** 3 + 3 * sin(pi / 12)) ** 3 + 3 * ((-4) * sin(pi / 12) ** 3 + 3 * sin(pi / 12)) = -4*(-4*sin(pi/12)**3 + 3*sin(pi/12))**3 - 12*sin(pi/12)**3 + 9*sin(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -4 * sin(pi/12) ** 3 + 3 * sin(pi/12),
{
have : sin(pi/4) = sin(3*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 4) ** 3 + 3 * sin(pi / 4) = -4*sin(pi/4)**3 + 3*sin(pi/4),
{
field_simp at *,
},
have : sin(3*pi/4) = -4 * sin(pi/4) ** 3 + 3 * sin(pi/4),
{
have : sin(3*pi/4) = sin(3*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_279 (h0 : cos(3*pi/2)≠ 0) (h1 : (2*cos(3*pi/2))≠ 0) (h2 : (2*sin(1499*pi))≠ 0) : sin(3*pi)/(2*sin(1499*pi))=- 4 * sin(pi/2) ** 3 + 3 * sin(pi/2):=
begin
have : cos(3*pi/2) = sin(1499*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/2) (750),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/2) = sin(3*pi) / ( 2 * cos(3*pi/2) ),
{
have : sin(3*pi) = sin(2*(3*pi/2)),
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


lemma Trigo_number_generalization_step2_280 : cos(6623*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos(6623 * pi / 6) = cos(6623*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(931*pi/6) = -cos(6623*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (931*pi/6) (629),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(931*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (77),
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


lemma Trigo_number_generalization_step2_281 : sin(2*pi) + sin(146*pi/3)=2*sin(7*pi/6)*sin(1846*pi/3):=
begin
have : sin(146 * pi / 3) + sin(2 * pi) = sin(2*pi) + sin(146*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(146*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/6) = sin(1846*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-5*pi/6) (307),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) + sin(2*pi) = 2 * sin(7*pi/6) * cos(-5*pi/6),
{
rw sin_add_sin,
have : sin(((pi/3) + (2*pi))/2) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (2*pi))/2) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_282 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : (cos(2*pi/3)+1)≠ 0) (h2 : (1+cos(2*pi/3))≠ 0) (h3 : (-cos(2743*pi/3)+1)≠ 0) (h4 : (1-cos(2743*pi/3))≠ 0) : sin(2*pi/3)/(1 - cos(2743*pi/3))=sqrt( 3 ):=
begin
have : sin(2 * pi / 3) / (-cos(2743 * pi / 3) + 1) = sin(2*pi/3)/(1 - cos(2743*pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -cos(2743*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (457),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_283 : sin(6*pi/5)*cos(-pi/5) + (-1 + 2*cos(3*pi/5)**2)*sin(-pi/5)=cos(1111*pi/2):=
begin
have : sin(6 * pi / 5) * cos(-pi / 5) + sin(-pi / 5) * (2 * cos(3 * pi / 5) ** 2 - 1) = sin(6*pi/5)*cos(-pi/5) + (-1 + 2*cos(3*pi/5)**2)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(6*pi/5) = 2 * cos(3*pi/5) ** 2 - 1,
{
have : cos(6*pi/5) = cos(2*(3*pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(6*pi/5) * cos(-pi/5) + sin(-pi/5) * cos(6*pi/5),
{
have : sin(pi) = sin((6*pi/5) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(1111*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (278),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_284 (h0 : cos(-pi/8)≠ 0) (h1 : (2*cos(-pi/8)**2)≠ 0) (h2 : (2*cos(-pi/8))≠ 0) : -sin(-pi/4)**2/(2*cos(-pi/8)**2) + 1=- sin(2725*pi/4):=
begin
have : 1 - 2 * (sin(-pi / 4) / (2 * cos(-pi / 8))) ** 2 = -sin(-pi/4)**2/(2*cos(-pi/8)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(-pi/4) / ( 2 * cos(-pi/8) ),
{
have : sin(-pi/4) = sin(2*(-pi/8)),
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
have : cos(-pi/4) = 1 - 2 * sin(-pi/8) ** 2,
{
have : cos(-pi/4) = cos(2*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - sin(2725*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (340),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_285 (h0 : tan(3267*pi/4)≠ 0) (h1 : cos(9805*pi/12)≠ 0) (h2 : cos(pi/3)≠ 0) (h3 : (1+tan(9805*pi/12)*tan(pi/3))≠ 0) (h4 : (-tan(pi/3)+tan(9805*pi/12))≠ 0) (h5 : ((tan(9805*pi/12)-tan(pi/3))/(1+tan(9805*pi/12)*tan(pi/3)))≠ 0) : (tan(pi/3)*tan(9805*pi/12) + 1)/(-tan(pi/3) + tan(9805*pi/12))=- 1:=
begin
have : 1 / ((tan(9805 * pi / 12) - tan(pi / 3)) / (1 + tan(9805 * pi / 12) * tan(pi / 3))) = (tan(pi/3)*tan(9805*pi/12) + 1)/(-tan(pi/3) + tan(9805*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3267*pi/4) = ( tan(9805*pi/12) - tan(pi/3) ) / ( 1 + tan(9805*pi/12) * tan(pi/3) ),
{
have : tan(3267*pi/4) = tan((9805*pi/12) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 1 / tan(3267*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (817),
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


lemma Trigo_number_generalization_step2_286 (h0 : tan(3907*pi/4)≠ 0) (h1 : cos((3907*pi/2)/2)≠ 0) (h2 : ((1-cos(3907*pi/2))/sin(3907*pi/2))≠ 0) (h3 : sin(3907*pi/2)≠ 0) (h4 : (1-cos(3907*pi/2))≠ 0) : -sin(3907*pi/2)/(1 - cos(3907*pi/2))=1:=
begin
have : (-1) / ((1 - cos(3907 * pi / 2)) / sin(3907 * pi / 2)) = -sin(3907*pi/2)/(1 - cos(3907*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3907*pi/4) = ( 1 - cos(3907*pi/2) ) / sin(3907*pi/2),
{
have : tan(3907*pi/4) = tan((3907*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(3907 * pi / 4) = -1/tan(3907*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(3907*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (976),
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


lemma Trigo_number_generalization_step2_287 : -sin(pi/3)**2 + sin(5063*pi/6)**2=- 1 / 2:=
begin
have : -sin(pi / 3) ** 2 + (-sin(5063 * pi / 6)) ** 2 = -sin(pi/3)**2 + sin(5063*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(5063*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (421),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(pi/3) ** 2 + cos(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_288 : -sin(2959*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(1125*pi/4) = sin(2959*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (1125*pi/4) (510),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -sin(1125*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (140),
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


lemma Trigo_number_generalization_step2_289 : -cos(136*pi)=cos(-2*pi)*cos(pi) - (sin(0)*cos(2*pi) - sin(2*pi)*cos(0))*sin(pi):=
begin
have : cos(-pi) = -cos(136*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi) * (sin(0) * cos(2 * pi) - sin(2 * pi) * cos(0)) + cos(pi) * cos((-2) * pi) = cos(-2*pi)*cos(pi) - (sin(0)*cos(2*pi) - sin(2*pi)*cos(0))*sin(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = sin(0) * cos(2*pi) - sin(2*pi) * cos(0),
{
have : sin(-2*pi) = sin((0) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = - sin(pi) * sin(-2*pi) + cos(pi) * cos(-2*pi),
{
have : cos(-pi) = cos((pi) + (-2*pi)),
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


lemma Trigo_number_generalization_step2_290 : sin(-7*pi/12)=-sin(pi/3)*sin(507*pi/4) - sin(-pi/4)*cos(5638*pi/3):=
begin
have : cos(-pi/4) = sin(507*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 4) * -cos(5638 * pi / 3) - sin(pi / 3) * cos(-pi / 4) = -sin(pi/3)*cos(-pi/4) - sin(-pi/4)*cos(5638*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(5638*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (939),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-7*pi/12) = sin(-pi/4) * cos(pi/3) - sin(pi/3) * cos(-pi/4),
{
have : sin(-7*pi/12) = sin((-pi/4) - (pi/3)),
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


lemma Trigo_number_generalization_step2_291 (h0 : cos(2953*pi/4)≠ 0) (h1 : (2*cos(2953*pi/4))≠ 0) : sin(2953*pi/2)/(2*cos(2953*pi/4))=sqrt( 2 ) / 2:=
begin
have : sin(2953*pi/4) = sin(2953*pi/2) / ( 2 * cos(2953*pi/4) ),
{
have : sin(2953*pi/2) = sin(2*(2953*pi/4)),
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
have : sin(pi/4) = sin(2953*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (369),
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


lemma Trigo_number_generalization_step2_292 : (-sin(pi/9)*cos(13*pi/36) + sin(13*pi/36)*cos(pi/9))*sin(pi/8)=-cos(pi/24)*cos(pi/3)/2 + sin(pi/24)*sin(pi/3)/2 + cos(pi/8)/2:=
begin
have : (sin(13 * pi / 36) * cos(pi / 9) - sin(pi / 9) * cos(13 * pi / 36)) * sin(pi / 8) = (-sin(pi/9)*cos(13*pi/36) + sin(13*pi/36)*cos(pi/9))*sin(pi/8),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(13*pi/36) * cos(pi/9) - sin(pi/9) * cos(13*pi/36),
{
have : sin(pi/4) = sin((13*pi/36) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 8) / 2 - (-sin(pi / 24) * sin(pi / 3) + cos(pi / 24) * cos(pi / 3)) / 2 = -cos(pi/24)*cos(pi/3)/2 + sin(pi/24)*sin(pi/3)/2 + cos(pi/8)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/8) = -sin(pi/24) * sin(pi/3) + cos(pi/24) * cos(pi/3),
{
have : cos(3*pi/8) = cos((pi/24) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) * sin(pi/8) = cos(pi/8) / 2 - cos(3*pi/8) / 2,
{
rw sin_mul_sin,
have : cos((pi/4) + (pi/8)) = cos(3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/4) - (pi/8)) = cos(pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_293 (h0 : sin(pi/3)≠ 0) (h1 : (2*sin(pi/3))≠ 0) : -cos(5129*pi/6)/(2*sin(pi/3))=1 / 2:=
begin
have : sin(2*pi/3) = -cos(5129*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (427),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_294 : -sin(1649*pi/6)**2 + cos(pi/6)**2=1 / 2:=
begin
have : sin(pi/6) = sin(1649*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (137),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_295 : -3*sin(7351*pi/18) + 4*sin(7351*pi/18)**3=1 / 2:=
begin
have : -((-4) * sin(7351 * pi / 18) ** 3 + 3 * sin(7351 * pi / 18)) = -3*sin(7351*pi/18) + 4*sin(7351*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(7351*pi/6) = -4 * sin(7351*pi/18) ** 3 + 3 * sin(7351*pi/18),
{
have : sin(7351*pi/6) = sin(3*(7351*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(7351*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (612),
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


lemma Trigo_number_generalization_step2_296 (h0 : tan(2705*pi/6)≠ 0) (h1 : tan(4333*pi/3)≠ 0) (h2 : ((-1)/tan(4333*pi/3))≠ 0) : tan(4333*pi/3)=- 1 / tan(959*pi/6):=
begin
have : (-1) / ((-1) / tan(4333 * pi / 3)) = tan(4333*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2705*pi/6) = -1 / tan(4333*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2705*pi/6) (993),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(2705 * pi / 6) = -1/tan(2705*pi/6),
{
field_simp at *,
},
have : tan(pi/3) = -1 / tan(2705*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (450),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = - 1 / tan(959*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (159),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_297 : (sin(-pi/2)*sin(pi/2) + cos(-pi/2)*cos(pi/2))**2=1 - cos(1741*pi/2)**2:=
begin
have : cos(-pi) = sin(-pi/2) * sin(pi/2) + cos(-pi/2) * cos(pi/2),
{
have : cos(-pi) = cos((-pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (-cos(1741 * pi / 2)) ** 2 = 1 - cos(1741*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = -cos(1741*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (434),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) ** 2 = 1 - sin(-pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_298 : (-(sin(-4*pi/45)*cos(pi/5) + sin(pi/5)*cos(-4*pi/45))*cos(19*pi/9) + sin(19*pi/9)*cos(pi/9))*cos(pi/3)=- sin(-5*pi/3) / 2 + sin(7*pi/3) / 2:=
begin
have : (-(sin((-4) * pi / 45) * cos(pi / 5) + sin(pi / 5) * cos((-4) * pi / 45)) * cos(19 * pi / 9) + sin(19 * pi / 9) * cos(pi / 9)) * cos(pi / 3) = (-(sin(-4*pi/45)*cos(pi/5) + sin(pi/5)*cos(-4*pi/45))*cos(19*pi/9) + sin(19*pi/9)*cos(pi/9))*cos(pi/3),
{
field_simp at *,
},
have : sin(pi/9) = sin(-4*pi/45) * cos(pi/5) + sin(pi/5) * cos(-4*pi/45),
{
have : sin(pi/9) = sin((-4*pi/45) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(19 * pi / 9) * cos(pi / 9) - sin(pi / 9) * cos(19 * pi / 9)) * cos(pi / 3) = (-sin(pi/9)*cos(19*pi/9) + sin(19*pi/9)*cos(pi/9))*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(19*pi/9) * cos(pi/9) - sin(pi/9) * cos(19*pi/9),
{
have : sin(2*pi) = sin((19*pi/9) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(pi/3) = - sin(-5*pi/3) / 2 + sin(7*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_299 (h0 : tan(11741*pi/8)≠ 0) : 1/tan(11741*pi/8)=- tan(3385*pi/8):=
begin
have : -((-1) / tan(11741 * pi / 8)) = 1/tan(11741*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(7209*pi/8) = -1 / tan(11741*pi/8),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7209*pi/8) (566),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = -tan(7209*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (901),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - tan(3385*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (423),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_300 : sin(938*pi/3)=sin(5366*pi/3):=
begin
have : cos(7799*pi/6) = sin(938*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7799*pi/6) (806),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(7799*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (649),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(5366*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (894),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_301 : sin(21827*pi/10)=cos(6469*pi/5):=
begin
have : - -sin(21827 * pi / 10) = sin(21827*pi/10),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(9186*pi/5) = -sin(21827*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (9186*pi/5) (172),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = -cos(9186*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/5) (918),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = cos(6469*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/5) (647),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_302 : sin(13267*pi/10)*cos(-8*pi/15) + sin(-8*pi/15)*sin(-pi/5)=2 * cos(-pi/6) ** 2 - 1:=
begin
have : cos((-8) * pi / 15) * sin(13267 * pi / 10) + sin((-8) * pi / 15) * sin(-pi / 5) = sin(13267*pi/10)*cos(-8*pi/15) + sin(-8*pi/15)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = sin(13267*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/5) (663),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-8) * pi / 15) * sin(-pi / 5) + cos((-8) * pi / 15) * cos(-pi / 5) = cos(-8*pi/15)*cos(-pi/5) + sin(-8*pi/15)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(-8*pi/15) * sin(-pi/5) + cos(-8*pi/15) * cos(-pi/5),
{
have : cos(-pi/3) = cos((-8*pi/15) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_number_generalization_step2_303 : -sin(1249*pi/3) - cos(1093*pi/10)=2 * sin(-pi/15) * cos(-4*pi/15):=
begin
have : sin(-pi/3) = -sin(1249*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (208),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = cos(1093*pi/10),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) - sin(-pi/5) = 2 * sin(-pi/15) * cos(-4*pi/15),
{
rw sin_sub_sin,
have : cos(((-pi/3) + (-pi/5))/2) = cos(-4*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (-pi/5))/2) = sin(-pi/15),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_304 : cos(8609*pi/6)**2=1 - sin(1681*pi/6)**2:=
begin
have : (-cos(8609 * pi / 6)) ** 2 = cos(8609*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -cos(8609*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (717),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (-sin(1681 * pi / 6)) ** 2 = 1 - sin(1681*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = -sin(1681*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (140),
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


lemma Trigo_number_generalization_step2_305 : sin(-pi/2)=(-2*cos(-pi/3)*cos(17539*pi/12) + 2*sin(-7*pi/12)*sin(-pi/3))*sin(-pi/4):=
begin
have : 2 * (-cos(17539 * pi / 12) * cos(-pi / 3) + sin((-7) * pi / 12) * sin(-pi / 3)) * sin(-pi / 4) = (-2*cos(-pi/3)*cos(17539*pi/12) + 2*sin(-7*pi/12)*sin(-pi/3))*sin(-pi/4),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-7*pi/12) = -cos(17539*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-7*pi/12) (730),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin(-pi / 4) * (sin((-7) * pi / 12) * sin(-pi / 3) + cos((-7) * pi / 12) * cos(-pi / 3)) = 2*(cos(-7*pi/12)*cos(-pi/3) + sin(-7*pi/12)*sin(-pi/3))*sin(-pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = sin(-7*pi/12) * sin(-pi/3) + cos(-7*pi/12) * cos(-pi/3),
{
have : cos(-pi/4) = cos((-7*pi/12) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step2_306 : cos(-pi/5)=-cos(18636*pi/5):=
begin
have : sin(20247*pi/10) = -cos(18636*pi/5),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (20247*pi/10) (851),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3387*pi/10) = sin(20247*pi/10),
{
rw sin_eq_sin_add_int_mul_two_pi (3387*pi/10) (843),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) = sin(3387*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/5) (169),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_307 (h0 : cos((-2*pi/5)/2)≠ 0) (h1 : sin((-2)*pi/5)≠ 0) (h2 : sin(-2*pi/5)≠ 0) : (sin(12419*pi/10) + 1)/sin(-2*pi/5)=- 1 / tan(3723*pi/10):=
begin
have : (1 - -sin(12419 * pi / 10)) / sin((-2) * pi / 5) = (sin(12419*pi/10) + 1)/sin(-2*pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = -sin(12419*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/5) (620),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos((-2) * pi / 5)) / sin((-2) * pi / 5) = (1 - cos(-2*pi/5))/sin(-2*pi/5),
{
field_simp at *,
},
have : tan(-pi/5) = ( 1 - cos(-2*pi/5) ) / sin(-2*pi/5),
{
have : tan(-pi/5) = tan((-2*pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = - 1 / tan(3723*pi/10),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/5) (372),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_308 : 3*cos(802*pi/3) - 4*cos(802*pi/3)**3=- 1:=
begin
have : -(4 * cos(802 * pi / 3) ** 3 - 3 * cos(802 * pi / 3)) = 3*cos(802*pi/3) - 4*cos(802*pi/3)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(802*pi) = 4 * cos(802*pi/3) ** 3 - 3 * cos(802*pi/3),
{
have : cos(802*pi) = cos(3*(802*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(802*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (400),
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


lemma Trigo_number_generalization_step2_309 : sin(2*pi)*cos(31781*pi/18) + cos(-19*pi/9)*cos(2*pi)=sin(19375*pi/18):=
begin
have : - -cos(31781 * pi / 18) * sin(2 * pi) + cos((-19) * pi / 9) * cos(2 * pi) = sin(2*pi)*cos(31781*pi/18) + cos(-19*pi/9)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-19*pi/9) = -cos(31781*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-19*pi/9) (881),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-19) * pi / 9) * sin(2 * pi) + cos((-19) * pi / 9) * cos(2 * pi) = -sin(-19*pi/9)*sin(2*pi) + cos(-19*pi/9)*cos(2*pi),
{
field_simp at *,
},
have : cos(-pi/9) = -sin(-19*pi/9) * sin(2*pi) + cos(-19*pi/9) * cos(2*pi),
{
have : cos(-pi/9) = cos((-19*pi/9) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = sin(19375*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (538),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_310 (h0 : sin(-pi/7)≠ 0) (h1 : (2*sin(-pi/7))≠ 0) : sin(-2*pi/7)/(2*sin(-pi/7))=sin(-1559*pi/14):=
begin
have : sin((-2) * pi / 7) / (2 * sin(-pi / 7)) = sin(-2*pi/7)/(2*sin(-pi/7)),
{
field_simp at *,
},
have : cos(-pi/7) = sin(-2*pi/7) / ( 2 * sin(-pi/7) ),
{
have : sin(-2*pi/7) = sin(2*(-pi/7)),
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
have : sin((-1559) * pi / 14) = sin(-1559*pi/14),
{
field_simp at *,
},
have : sin(22321*pi/14) = sin(-1559*pi/14),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (22321*pi/14) (741),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/7) = sin(22321*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/7) (797),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_311 : cos(pi/2)=cos(577*pi/2):=
begin
have : -1 + 2 * (cos(pi / 2) / 2 + 1 / 2) = cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) ** 2 = cos(pi/2) / 2 + 1 / 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/2) = cos(577*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (144),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_312 : -sin(19319*pi/10)=-sin(pi/5)**2 + cos(6609*pi/5)**2:=
begin
have : cos(pi/5) = cos(6609*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/5) (661),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/5) = -sin(19319*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/5) (965),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/5) = - sin(pi/5) ** 2 + cos(pi/5) ** 2,
{
have : cos(2*pi/5) = cos(2*(pi/5)),
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


lemma Trigo_number_generalization_step2_313 : cos(461*pi/2)**2=1 - sin(3189*pi/2)**2:=
begin
have : (-cos(461 * pi / 2)) ** 2 = cos(461*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(461*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (115),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (-sin(3189 * pi / 2)) ** 2 = 1 - sin(3189*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -sin(3189*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (796),
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


lemma Trigo_number_generalization_step2_314 : cos(4607*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(721*pi/3) = cos(4607*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (721*pi/3) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(721*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (120),
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


lemma Trigo_number_generalization_step2_315 : 2*(3*sin(-pi/48) - 4*sin(-pi/48)**3)*cos(-pi/16)=sin(207*pi/8):=
begin
have : 2 * ((-4) * sin(-pi / 48) ** 3 + 3 * sin(-pi / 48)) * cos(-pi / 16) = 2*(3*sin(-pi/48) - 4*sin(-pi/48)**3)*cos(-pi/16),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/16) = -4 * sin(-pi/48) ** 3 + 3 * sin(-pi/48),
{
have : sin(-pi/16) = sin(3*(-pi/48)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = 2 * sin(-pi/16) * cos(-pi/16),
{
have : sin(-pi/8) = sin(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(207*pi/8),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/8) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_316 : -sin(6436*pi/5)*cos(pi) + sin(pi)*cos(6436*pi/5)=sin(3259*pi/5):=
begin
have : -(sin(6436 * pi / 5) * cos(pi) - sin(pi) * cos(6436 * pi / 5)) = -sin(6436*pi/5)*cos(pi) + sin(pi)*cos(6436*pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(6431*pi/5) = sin(6436*pi/5) * cos(pi) - sin(pi) * cos(6436*pi/5),
{
have : sin(6431*pi/5) = sin((6436*pi/5) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = -sin(6431*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/5) (643),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = sin(3259*pi/5),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/5) (326),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_317 : cos(pi/3)=-(-4*sin(pi/18)**3 + 3*sin(pi/18))**2 - sin(pi/6)**2 + 1:=
begin
have : -((-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18)) ** 2 + (1 - sin(pi / 6) ** 2) = -(-4*sin(pi/18)**3 + 3*sin(pi/18))**2 - sin(pi/6)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) ** 2 = 1 - sin(pi/6) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : -((-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18)) ** 2 + cos(pi / 6) ** 2 = -(-4*sin(pi/18)**3 + 3*sin(pi/18))**2 + cos(pi/6)**2,
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


lemma Trigo_number_generalization_step2_318 : cos(pi/7)=4*sin(12245*pi/56)*cos(12245*pi/56)*cos(12245*pi/28):=
begin
have : 2 * (2 * sin(12245 * pi / 56) * cos(12245 * pi / 56)) * cos(12245 * pi / 28) = 4*sin(12245*pi/56)*cos(12245*pi/56)*cos(12245*pi/28),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : sin(12245*pi/28) = 2 * sin(12245*pi/56) * cos(12245*pi/56),
{
have : sin(12245*pi/28) = sin(2*(12245*pi/56)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(12245*pi/14) = 2 * sin(12245*pi/28) * cos(12245*pi/28),
{
have : sin(12245*pi/14) = sin(2*(12245*pi/28)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = sin(12245*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/7) (437),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_319 : cos(17045*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(5155*pi/12) = cos(17045*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5155*pi/12) (925),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(5155*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (214),
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


lemma Trigo_number_generalization_step2_320 (h0 : cos(pi/12)≠ 0) : -sin(21013*pi/12)/cos(pi/12)=2 - sqrt( 3 ):=
begin
have : sin(pi/12) = -sin(21013*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/12) (875),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = sin(pi/12) / cos(pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_321 (h0 : sin(18839*pi/14)≠ 0) (h1 : (2*sin(18839*pi/14))≠ 0) : -sin(6320*pi/7)=-sin(18839*pi/7)/(2*sin(18839*pi/14)):=
begin
have : sin(-pi/7) = -sin(6320*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/7) (451),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(18839 * pi / 7) / (2 * sin(18839 * pi / 14))) = -sin(18839*pi/7)/(2*sin(18839*pi/14)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(18839*pi/14) = sin(18839*pi/7) / ( 2 * sin(18839*pi/14) ),
{
have : sin(18839*pi/7) = sin(2*(18839*pi/14)),
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
have : sin(-pi/7) = - cos(18839*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (672),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_322 : -sin(pi)*cos(8093*pi/6) - sin(8093*pi/6)*cos(pi)=1 / 2:=
begin
have : -(sin(8093 * pi / 6) * cos(pi) + sin(pi) * cos(8093 * pi / 6)) = -sin(pi)*cos(8093*pi/6) - sin(8093*pi/6)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(8099*pi/6) = sin(8093*pi/6) * cos(pi) + sin(pi) * cos(8093*pi/6),
{
have : sin(8099*pi/6) = sin((8093*pi/6) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(8099*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (674),
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


lemma Trigo_number_generalization_step2_323 (h0 : cos(pi/2)≠ 0) (h1 : (1-tan(pi/2)**2)≠ 0) (h2 : cos((pi)/2)≠ 0) (h3 : (cos(pi)+1)≠ 0) (h4 : (1-(sin(pi)/(1+cos(pi)))**2)≠ 0) (h5 : (1+cos(pi))≠ 0) (h6 : ((-sin(pi)**2/(cos(pi)+1)**2+1)*(cos(pi)+1))≠ 0) : 2*sin(pi)/((-sin(pi)**2/(cos(pi) + 1)**2 + 1)*(cos(pi) + 1))=0:=
begin
have : 2 * (sin(pi) / (1 + cos(pi))) / (1 - (sin(pi) / (1 + cos(pi))) ** 2) = 2*sin(pi)/((-sin(pi)**2/(cos(pi) + 1)**2 + 1)*(cos(pi) + 1)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = sin(pi) / ( 1 + cos(pi) ),
{
have : tan(pi/2) = tan((pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 2 * tan(pi/2) / ( 1 - tan(pi/2) ** 2 ),
{
have : tan(pi) = tan(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_324 : cos(2*pi)=1 - 2*(sin(-pi/9)*cos(91*pi/9) + sin(91*pi/9)*cos(-pi/9))**2:=
begin
have : 1 - 2 * (sin(91 * pi / 9) * cos(-pi / 9) + sin(-pi / 9) * cos(91 * pi / 9)) ** 2 = 1 - 2*(sin(-pi/9)*cos(91*pi/9) + sin(91*pi/9)*cos(-pi/9))**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(10*pi) = sin(91*pi/9) * cos(-pi/9) + sin(-pi/9) * cos(91*pi/9),
{
have : sin(10*pi) = sin((91*pi/9) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - 2 * (-sin(10 * pi)) ** 2 = 1 - 2*sin(10*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -sin(10*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = 1 - 2 * sin(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_325 : -4*cos(2657*pi/18)**3 + 3*cos(2657*pi/18)=sqrt( 3 ) / 2:=
begin
have : -(4 * cos(2657 * pi / 18) ** 3 - 3 * cos(2657 * pi / 18)) = -4*cos(2657*pi/18)**3 + 3*cos(2657*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2657*pi/6) = 4 * cos(2657*pi/18) ** 3 - 3 * cos(2657*pi/18),
{
have : cos(2657*pi/6) = cos(3*(2657*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(2657*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (221),
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


lemma Trigo_number_generalization_step2_326 : (1 - 2*sin(pi/14)**2)*cos(-6*pi/7) + sin(-6*pi/7)*sin(pi/7)=cos(325*pi):=
begin
have : cos((-6) * pi / 7) * (1 - 2 * sin(pi / 14) ** 2) + sin((-6) * pi / 7) * sin(pi / 7) = (1 - 2*sin(pi/14)**2)*cos(-6*pi/7) + sin(-6*pi/7)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = 1 - 2 * sin(pi/14) ** 2,
{
have : cos(pi/7) = cos(2*(pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin((-6) * pi / 7) * sin(pi / 7) + cos((-6) * pi / 7) * cos(pi / 7) = cos(-6*pi/7)*cos(pi/7) + sin(-6*pi/7)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(-6*pi/7) * sin(pi/7) + cos(-6*pi/7) * cos(pi/7),
{
have : cos(-pi) = cos((-6*pi/7) - (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(325*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (162),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_327 : sin(13*pi/12)*sin(6059*pi/4) + sin(-pi/4)*cos(13*pi/12)=1 / 2:=
begin
have : cos(-pi/4) = sin(6059*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (757),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(13*pi/12) * cos(-pi/4) + sin(-pi/4) * cos(13*pi/12),
{
have : sin(5*pi/6) = sin((13*pi/12) + (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_328 (h0 : cos(-9*pi/8)≠ 0) (h1 : cos(-pi/8)≠ 0) (h2 : (1+tan((-9)*pi/8)*tan(-pi/8))≠ 0) (h3 : (tan(-9*pi/8)*tan(-pi/8)+1)≠ 0) (h4 : cos((-pi/4)/2)≠ 0) (h5 : sin(-pi/4)≠ 0) (h6 : (tan((-9)*pi/8)*((1-cos(-pi/4))/sin(-pi/4))+1)≠ 0) (h7 : ((1-cos(-pi/4))*tan(-9*pi/8)/sin(-pi/4)+1)≠ 0) : (tan(-9*pi/8) - (1 - cos(-pi/4))/sin(-pi/4))/((1 - cos(-pi/4))*tan(-9*pi/8)/sin(-pi/4) + 1)=- tan(91*pi):=
begin
have : (tan((-9) * pi / 8) - (1 - cos(-pi / 4)) / sin(-pi / 4)) / (tan((-9) * pi / 8) * ((1 - cos(-pi / 4)) / sin(-pi / 4)) + 1) = (tan(-9*pi/8) - (1 - cos(-pi/4))/sin(-pi/4))/((1 - cos(-pi/4))*tan(-9*pi/8)/sin(-pi/4) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = ( 1 - cos(-pi/4) ) / sin(-pi/4),
{
have : tan(-pi/8) = tan((-pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan((-9) * pi / 8) - tan(-pi / 8)) / (1 + tan((-9) * pi / 8) * tan(-pi / 8)) = (tan(-9*pi/8) - tan(-pi/8))/(tan(-9*pi/8)*tan(-pi/8) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = ( tan(-9*pi/8) - tan(-pi/8) ) / ( 1 + tan(-9*pi/8) * tan(-pi/8) ),
{
have : tan(-pi) = tan((-9*pi/8) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - tan(91*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_329 : -2*sin(1513*pi)*cos(pi)=- sin(1817*pi):=
begin
have : 2 * -sin(1513 * pi) * cos(pi) = -2*sin(1513*pi)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(1513*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (757),
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
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(1817*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (907),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_330 : -sin(794*pi)=-1 + 2*cos(-pi/4)**2:=
begin
have : cos(-pi/2) = -sin(794*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (396),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - cos(-pi / 4) ** 2) + cos(-pi / 4) ** 2 = -1 + 2*cos(-pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) ** 2 = 1 - cos(-pi/4) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(-pi/4) ** 2 + cos(-pi/4) ** 2,
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
rw this,
end


lemma Trigo_number_generalization_step2_331 (h0 : cos(pi)≠ 0) : sin(1956*pi)/cos(pi)=0:=
begin
have : sin(pi) = sin(1956*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (978),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_332 : -3 + 6*sin(pi/72)**2 + 4*(1 - 2*sin(pi/72)**2)**3=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-3) * (1 - 2 * sin(pi / 72) ** 2) + 4 * (1 - 2 * sin(pi / 72) ** 2) ** 3 = -3 + 6*sin(pi/72)**2 + 4*(1 - 2*sin(pi/72)**2)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/36) = 1 - 2 * sin(pi/72) ** 2,
{
have : cos(pi/36) = cos(2*(pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : 4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36) = -3*cos(pi/36) + 4*cos(pi/36)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = 4 * cos(pi/36) ** 3 - 3 * cos(pi/36),
{
have : cos(pi/12) = cos(3*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_333 : 4*cos(2239*pi/6)**3 - 3*cos(2239*pi/6)=4 * cos(pi/2) ** 3 - 3 * cos(pi/2):=
begin
have : cos(2239*pi/2) = 4 * cos(2239*pi/6) ** 3 - 3 * cos(2239*pi/6),
{
have : cos(2239*pi/2) = cos(3*(2239*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/2) = cos(2239*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/2) (559),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/2) = 4 * cos(pi/2) ** 3 - 3 * cos(pi/2),
{
have : cos(3*pi/2) = cos(3*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_334 : -sin(-3893*pi/6)=1 / 2:=
begin
have : -sin((-3893) * pi / 6) = -sin(-3893*pi/6),
{
field_simp at *,
},
have : cos(2638*pi/3) = sin(-3893*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2638*pi/3) (115),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(2638*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (439),
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


lemma Trigo_number_generalization_step2_335 : (cos(-pi/6)*cos(21611*pi/12) - sin(-pi/6)*sin(21611*pi/12))**2=1 / 2 - cos(pi/2) / 2:=
begin
have : (-sin(21611 * pi / 12) * sin(-pi / 6) + cos(21611 * pi / 12) * cos(-pi / 6)) ** 2 = (cos(-pi/6)*cos(21611*pi/12) - sin(-pi/6)*sin(21611*pi/12))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7203*pi/4) = -sin(21611*pi/12) * sin(-pi/6) + cos(21611*pi/12) * cos(-pi/6),
{
have : cos(7203*pi/4) = cos((21611*pi/12) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(7203 * pi / 4)) ** 2 = cos(7203*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(7203*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (900),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) ** 2 = 1 / 2 - cos(pi/2) / 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
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


lemma Trigo_number_generalization_step2_336 : 4*cos(10483*pi/9)**3 - 3*cos(10483*pi/9)=1 / 2:=
begin
have : (-4) * (-cos(10483 * pi / 9)) ** 3 + 3 * -cos(10483 * pi / 9) = 4*cos(10483*pi/9)**3 - 3*cos(10483*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = -cos(10483*pi/9),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (582),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(5 * pi / 18) ** 3 + 3 * sin(5 * pi / 18) = -4*sin(5*pi/18)**3 + 3*sin(5*pi/18),
{
field_simp at *,
},
have : sin(5*pi/6) = -4 * sin(5*pi/18) ** 3 + 3 * sin(5*pi/18),
{
have : sin(5*pi/6) = sin(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_337 (h0 : cos(pi/3)≠ 0) : tan(pi/3)=(sin(-pi/5)*cos(8*pi/15) + 2*sin(4*pi/15)*cos(-pi/5)*cos(4*pi/15))/cos(pi/3):=
begin
have : (sin(-pi / 5) * cos(8 * pi / 15) + 2 * sin(4 * pi / 15) * cos(4 * pi / 15) * cos(-pi / 5)) / cos(pi / 3) = (sin(-pi/5)*cos(8*pi/15) + 2*sin(4*pi/15)*cos(-pi/5)*cos(4*pi/15))/cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(8*pi/15) = 2 * sin(4*pi/15) * cos(4*pi/15),
{
have : sin(8*pi/15) = sin(2*(4*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : (sin(8 * pi / 15) * cos(-pi / 5) + sin(-pi / 5) * cos(8 * pi / 15)) / cos(pi / 3) = (sin(-pi/5)*cos(8*pi/15) + sin(8*pi/15)*cos(-pi/5))/cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = sin(8*pi/15) * cos(-pi/5) + sin(-pi/5) * cos(8*pi/15),
{
have : sin(pi/3) = sin((8*pi/15) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_338 (h0 : sin(437*pi/16)≠ 0) (h1 : (2*sin(437*pi/16)**2)≠ 0) (h2 : (2*sin(437*pi/16))≠ 0) : sin(pi/8)=-sin(437*pi/8)**2/(2*sin(437*pi/16)**2) + 1:=
begin
have : 1 - 2 * (sin(437 * pi / 8) / (2 * sin(437 * pi / 16))) ** 2 = -sin(437*pi/8)**2/(2*sin(437*pi/16)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(437*pi/16) = sin(437*pi/8) / ( 2 * sin(437*pi/16) ),
{
have : sin(437*pi/8) = sin(2*(437*pi/16)),
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
have : -(2 * cos(437 * pi / 16) ** 2 - 1) = 1 - 2*cos(437*pi/16)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(437*pi/8) = 2 * cos(437*pi/16) ** 2 - 1,
{
have : cos(437*pi/8) = cos(2*(437*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) = - cos(437*pi/8),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/8) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_339 : -(3*sin(-pi/36) - 4*sin(-pi/36)**3)**2 + cos(-pi/12)**2=- cos(8561*pi/6):=
begin
have : -((-4) * sin(-pi / 36) ** 3 + 3 * sin(-pi / 36)) ** 2 + cos(-pi / 12) ** 2 = -(3*sin(-pi/36) - 4*sin(-pi/36)**3)**2 + cos(-pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = -4 * sin(-pi/36) ** 3 + 3 * sin(-pi/36),
{
have : sin(-pi/12) = sin(3*(-pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/12) ** 2 + cos(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(8561*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (713),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_340 : cos(pi/3)*cos(7355*pi/4)=- sin(7*pi/12) / 2 + sin(pi/12) / 2:=
begin
have : cos(7355 * pi / 4) * cos(pi / 3) = cos(pi/3)*cos(7355*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(637*pi/4) = cos(7355*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (637*pi/4) (839),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(637*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/4) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * cos(pi/3) = - sin(7*pi/12) / 2 + sin(pi/12) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/4)) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/4)) = sin(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_341 : -cos(3719*pi/2)=0:=
begin
have : cos(37*pi/2) = -cos(3719*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (37*pi/2) (920),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(37*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (9),
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


lemma Trigo_number_generalization_step2_342 : sin(-22625*pi/24)=sin(-pi/8) * cos(pi/6) - sin(pi/6) * cos(-pi/8):=
begin
have : sin((-22625) * pi / 24) = sin(-22625*pi/24),
{
field_simp at *,
},
have : sin(44153*pi/24) = sin(-22625*pi/24),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (44153*pi/24) (448),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/24) = sin(44153*pi/24),
{
rw sin_eq_sin_add_int_mul_two_pi (-7*pi/24) (920),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/24) = sin(-pi/8) * cos(pi/6) - sin(pi/6) * cos(-pi/8),
{
have : sin(-7*pi/24) = sin((-pi/8) - (pi/6)),
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


lemma Trigo_number_generalization_step2_343 (h0 : sin(6549*pi/4)≠ 0) (h1 : (2*sin(6549*pi/4))≠ 0) : -sin(6549*pi/2)/(2*sin(6549*pi/4))=sqrt( 2 ) / 2:=
begin
have : -(sin(6549 * pi / 2) / (2 * sin(6549 * pi / 4))) = -sin(6549*pi/2)/(2*sin(6549*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(6549*pi/4) = sin(6549*pi/2) / ( 2 * sin(6549*pi/4) ),
{
have : sin(6549*pi/2) = sin(2*(6549*pi/4)),
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
have : cos(pi/4) = -cos(6549*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (818),
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


lemma Trigo_number_generalization_step2_344 (h0 : (-sin(-pi/4)**2+cos(-pi/4)**2)≠ 0) (h1 : (-(-sin(601*pi/4))**2+cos(-pi/4)**2)≠ 0) (h2 : (-sin(601*pi/4)**2+cos(-pi/4)**2)≠ 0) : sin(-pi/2)/(-sin(601*pi/4)**2 + cos(-pi/4)**2)=tan(-pi/2):=
begin
have : sin(-pi / 2) / (-(-sin(601 * pi / 4)) ** 2 + cos(-pi / 4) ** 2) = sin(-pi/2)/(-sin(601*pi/4)**2 + cos(-pi/4)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -sin(601*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
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
have : sin(-pi/2) / cos(-pi/2) = tan(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_345 : cos(pi/2)*cos(23027*pi/12) + sin(pi/2)*cos(-5*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(23027 * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12) = cos(pi/2)*cos(23027*pi/12) + sin(pi/2)*cos(-5*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/12) = cos(23027*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-5*pi/12) (959),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12) = sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12),
{
field_simp at *,
},
have : sin(pi/12) = sin(-5*pi/12) * cos(pi/2) + sin(pi/2) * cos(-5*pi/12),
{
have : sin(pi/12) = sin((-5*pi/12) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_346 (h0 : cos(pi/6)≠ 0) (h1 : (1-tan(pi/6)**2)≠ 0) (h2 : tan(706*pi/3)≠ 0) (h3 : (1-(1/tan(706*pi/3))**2)≠ 0) (h4 : ((1-1/tan(706*pi/3)**2)*tan(706*pi/3))≠ 0) : 2/((1 - 1/tan(706*pi/3)**2)*tan(706*pi/3))=sqrt( 3 ):=
begin
have : 2 * (1 / tan(706 * pi / 3)) / (1 - (1 / tan(706 * pi / 3)) ** 2) = 2/((1 - 1/tan(706*pi/3)**2)*tan(706*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(706*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (235),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 2 * tan(pi/6) / ( 1 - tan(pi/6) ** 2 ),
{
have : tan(pi/3) = tan(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_347 : sin(-5*pi/4)*cos(-pi/4) - sin(-pi/4)*cos(2881*pi/4)=- 4 * sin(-pi/2) ** 3 + 3 * sin(-pi/2):=
begin
have : sin(-pi / 4) * -cos(2881 * pi / 4) + sin((-5) * pi / 4) * cos(-pi / 4) = sin(-5*pi/4)*cos(-pi/4) - sin(-pi/4)*cos(2881*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/4) = -cos(2881*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-5*pi/4) (359),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 4) * cos(-pi / 4) + sin(-pi / 4) * cos((-5) * pi / 4) = sin(-pi/4)*cos(-5*pi/4) + sin(-5*pi/4)*cos(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2) = sin(-5*pi/4) * cos(-pi/4) + sin(-pi/4) * cos(-5*pi/4),
{
have : sin(-3*pi/2) = sin((-5*pi/4) + (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step2_348 : 4*sin(4319*pi/9)**3 - 3*sin(4319*pi/9)=sqrt( 3 ) / 2:=
begin
have : -((-4) * sin(4319 * pi / 9) ** 3 + 3 * sin(4319 * pi / 9)) = 4*sin(4319*pi/9)**3 - 3*sin(4319*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4319*pi/3) = -4 * sin(4319*pi/9) ** 3 + 3 * sin(4319*pi/9),
{
have : sin(4319*pi/3) = sin(3*(4319*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(4319*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (719),
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


lemma Trigo_number_generalization_step2_349 (h0 : cos((9467*pi/6)/2)≠ 0) (h1 : sin(9467*pi/6)≠ 0) : -(1 - cos(9467*pi/6))/sin(9467*pi/6)=2 - sqrt( 3 ):=
begin
have : -((1 - cos(9467 * pi / 6)) / sin(9467 * pi / 6)) = -(1 - cos(9467*pi/6))/sin(9467*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(9467*pi/12) = ( 1 - cos(9467*pi/6) ) / sin(9467*pi/6),
{
have : tan(9467*pi/12) = tan((9467*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(9467*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (789),
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


lemma Trigo_number_generalization_step2_350 : cos(3116*pi/3)=- 1 / 2:=
begin
have : cos(734*pi/3) = cos(3116*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (734*pi/3) (397),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = cos(734*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (122),
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


lemma Trigo_number_generalization_step2_351 (h0 : cos((5806*pi/3)/2)≠ 0) (h1 : sin(5806*pi/3)≠ 0) : (1 - cos(5806*pi/3))/sin(5806*pi/3)=- sqrt( 3 ):=
begin
have : tan(2903*pi/3) = ( 1 - cos(5806*pi/3) ) / sin(5806*pi/3),
{
have : tan(2903*pi/3) = tan((5806*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = tan(2903*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (2*pi/3) (967),
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


lemma Trigo_number_generalization_step2_352 : sin(-pi/7)*cos(2*pi/63) + cos(1869*pi/2) + sin(2*pi/63)*cos(-pi/7)=2 * sin(-5*pi/9) * cos(4*pi/9):=
begin
have : sin(2 * pi / 63) * cos(-pi / 7) + sin(-pi / 7) * cos(2 * pi / 63) + cos(1869 * pi / 2) = sin(-pi/7)*cos(2*pi/63) + cos(1869*pi/2) + sin(2*pi/63)*cos(-pi/7),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(2*pi/63) * cos(-pi/7) + sin(-pi/7) * cos(2*pi/63),
{
have : sin(-pi/9) = sin((2*pi/63) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(1869*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (467),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) + sin(-pi) = 2 * sin(-5*pi/9) * cos(4*pi/9),
{
rw sin_add_sin,
have : sin(((-pi/9) + (-pi))/2) = sin(-5*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (-pi))/2) = cos(4*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_353 (h0 : (4*cos(-pi/18)**3-3*cos(-pi/18))≠ 0) (h1 : (-3*cos(-pi/18)+4*cos(-pi/18)**3)≠ 0) (h2 : ((-3)*cos(-pi/18)+4*cos(-pi/18)**3)≠ 0) : tan(-pi/6)=-sin(10825*pi/6)/(-3*cos(-pi/18) + 4*cos(-pi/18)**3):=
begin
have : -sin(10825 * pi / 6) / ((-3) * cos(-pi / 18) + 4 * cos(-pi / 18) ** 3) = -sin(10825*pi/6)/(-3*cos(-pi/18) + 4*cos(-pi/18)**3),
{
field_simp at *,
},
have : sin(-pi/6) = -sin(10825*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (902),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 6) / (4 * cos(-pi / 18) ** 3 - 3 * cos(-pi / 18)) = sin(-pi/6)/(-3*cos(-pi/18) + 4*cos(-pi/18)**3),
{
field_simp at *,
repeat {left},
ring,
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
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_354 (h0 : cos(-pi/9)≠ 0) (h1 : (2*cos(-pi/9))≠ 0) : -sin(14006*pi/9)*cos(-pi/2)/(2*cos(-pi/9))=- sin(-7*pi/18) / 2 + sin(-11*pi/18) / 2:=
begin
have : sin(-2*pi/9) = -sin(14006*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi/9) (778),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi / 9) / (2 * cos(-pi / 9)) * cos(-pi / 2) = sin(-2*pi/9)*cos(-pi/2)/(2*cos(-pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(-2*pi/9) / ( 2 * cos(-pi/9) ),
{
have : sin(-2*pi/9) = sin(2*(-pi/9)),
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
have : sin(-pi/9) * cos(-pi/2) = - sin(-7*pi/18) / 2 + sin(-11*pi/18) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (-pi/9)) = sin(-11*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (-pi/9)) = sin(-7*pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_355 : cos(6893*pi/2)=- cos(163*pi/2):=
begin
have : - -cos(6893 * pi / 2) = cos(6893*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1510*pi) = -cos(6893*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1510*pi) (968),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(1510*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (754),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - cos(163*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_356 : -3*cos(13717*pi/9) + 4*cos(13717*pi/9)**3=- cos(1462*pi/3):=
begin
have : (-3) * cos(13717 * pi / 9) + 4 * cos(13717 * pi / 9) ** 3 = -3*cos(13717*pi/9) + 4*cos(13717*pi/9)**3,
{
field_simp at *,
},
have : cos(pi/9) = cos(13717*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/9) (762),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/3) = - cos(1462*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (243),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_357 : -cos(-3019*pi/14)*cos(-pi/5)=- sin(-2*pi/35) / 2 + sin(-12*pi/35) / 2:=
begin
have : -cos((-3019) * pi / 14) * cos(-pi / 5) = -cos(-3019*pi/14)*cos(-pi/5),
{
field_simp at *,
},
have : sin(6588*pi/7) = -cos(-3019*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (6588*pi/7) (362),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = sin(6588*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/7) (470),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) * cos(-pi/5) = - sin(-2*pi/35) / 2 + sin(-12*pi/35) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/5) + (-pi/7)) = sin(-12*pi/35),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/5) - (-pi/7)) = sin(-2*pi/35),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_358 : -sin(-pi/7)*sin(13*pi/42) + (sin(pi/42)*sin(pi/6) + cos(pi/42)*cos(pi/6))*cos(13*pi/42)=sqrt( 3 ) / 2:=
begin
have : cos(-pi/7) = sin(pi/42) * sin(pi/6) + cos(pi/42) * cos(pi/6),
{
have : cos(-pi/7) = cos((pi/42) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(13 * pi / 42) * sin(-pi / 7) + cos(13 * pi / 42) * cos(-pi / 7) = -sin(-pi/7)*sin(13*pi/42) + cos(-pi/7)*cos(13*pi/42),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(13*pi/42) * sin(-pi/7) + cos(13*pi/42) * cos(-pi/7),
{
have : cos(pi/6) = cos((13*pi/42) + (-pi/7)),
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


lemma Trigo_number_generalization_step2_359 (h0 : tan(791*pi/6)≠ 0) (h1 : tan(1283*pi/3)≠ 0) (h2 : (1/tan(1283*pi/3))≠ 0) : -tan(1283*pi/3)=sqrt( 3 ):=
begin
have : (-1) / (1 / tan(1283 * pi / 3)) = -tan(1283*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(791*pi/6) = 1 / tan(1283*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (791*pi/6) (559),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(791 * pi / 6) = -1/tan(791*pi/6),
{
field_simp at *,
},
have : tan(pi/3) = -1 / tan(791*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (131),
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


lemma Trigo_number_generalization_step2_360 : -1 + 2*(-sin(-pi/24)**2 + cos(-pi/24)**2)**2=- cos(4807*pi/6):=
begin
have : cos(-pi/12) = -sin(-pi/24) ** 2 + cos(-pi/24) ** 2,
{
have : cos(-pi/12) = cos(2*(-pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(-pi/6) = - cos(4807*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (400),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_361 (h0 : cos(pi/4)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan(pi/4)*tan(-pi/2))≠ 0) (h3 : (tan(-pi/2)*tan(pi/4)+1)≠ 0) (h4 : tan(384*pi)≠ 0) (h5 : (1/tan(384*pi)*tan(pi/4)+1)≠ 0) (h6 : (1+tan(pi/4)/tan(384*pi))≠ 0) : (-1/tan(384*pi) + tan(pi/4))/(1 + tan(pi/4)/tan(384*pi))=- 1:=
begin
have : (tan(pi / 4) - 1 / tan(384 * pi)) / (1 / tan(384 * pi) * tan(pi / 4) + 1) = (-1/tan(384*pi) + tan(pi/4))/(1 + tan(pi/4)/tan(384*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = 1 / tan(384*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/2) (383),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 4) - tan(-pi / 2)) / (1 + tan(pi / 4) * tan(-pi / 2)) = (tan(pi/4) - tan(-pi/2))/(tan(-pi/2)*tan(pi/4) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = ( tan(pi/4) - tan(-pi/2) ) / ( 1 + tan(pi/4) * tan(-pi/2) ),
{
have : tan(3*pi/4) = tan((pi/4) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_362 : -sin(5756*pi/3)=- sqrt( 3 ) / 2:=
begin
have : sin(5204*pi/3) = sin(5756*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (5204*pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(5204*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (867),
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


lemma Trigo_number_generalization_step2_363 : cos(pi) ** 2=-4*sin(96*pi)**2*cos(96*pi)**2 + 1:=
begin
have : 1 - (2 * sin(96 * pi) * cos(96 * pi)) ** 2 = -4*sin(96*pi)**2*cos(96*pi)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(192*pi) = 2 * sin(96*pi) * cos(96*pi),
{
have : sin(192*pi) = sin(2*(96*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = sin(192*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (96),
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


lemma Trigo_number_generalization_step2_364 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) (h2 : (sin(11*pi/21)*cos(pi/7)+sin(pi/7)*cos(11*pi/21))≠ 0) (h3 : (sin(pi/7)*cos(11*pi/21)+sin(11*pi/21)*cos(pi/7))≠ 0) : (1 - cos(2*pi/3))/(sin(pi/7)*cos(11*pi/21) + sin(11*pi/21)*cos(pi/7))=sqrt( 3 ):=
begin
have : (1 - cos(2 * pi / 3)) / (sin(11 * pi / 21) * cos(pi / 7) + sin(pi / 7) * cos(11 * pi / 21)) = (1 - cos(2*pi/3))/(sin(pi/7)*cos(11*pi/21) + sin(11*pi/21)*cos(pi/7)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(11*pi/21) * cos(pi/7) + sin(pi/7) * cos(11*pi/21),
{
have : sin(2*pi/3) = sin((11*pi/21) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( 1 - cos(2*pi/3) ) / sin(2*pi/3),
{
have : tan(pi/3) = tan((2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_365 : -cos(82*pi/3)=1 / 2:=
begin
have : sin(9265*pi/6) = -cos(82*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (9265*pi/6) (785),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(9265*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (772),
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


lemma Trigo_number_generalization_step2_366 (h0 : tan(1227*pi/4)≠ 0) (h1 : cos((1227*pi/2)/2)≠ 0) (h2 : sin(1227*pi/2)≠ 0) (h3 : (1-cos(1227*pi/2))≠ 0) (h4 : ((1-cos(1227*pi/2))/sin(1227*pi/2))≠ 0) : sin(1227*pi/2)/(1 - cos(1227*pi/2))=- 1:=
begin
have : 1 / ((1 - cos(1227 * pi / 2)) / sin(1227 * pi / 2)) = sin(1227*pi/2)/(1 - cos(1227*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1227*pi/4) = ( 1 - cos(1227*pi/2) ) / sin(1227*pi/2),
{
have : tan(1227*pi/4) = tan((1227*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 1 / tan(1227*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (307),
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


lemma Trigo_number_generalization_step2_367 : (sin(-6*pi/7)*cos(-pi/7) + sin(-pi/7)*cos(-6*pi/7))*cos(3903*pi/8)=sin(-7*pi/8) / 2 + sin(-9*pi/8) / 2:=
begin
have : (sin((-6) * pi / 7) * cos(-pi / 7) + sin(-pi / 7) * cos((-6) * pi / 7)) * cos(3903 * pi / 8) = (sin(-6*pi/7)*cos(-pi/7) + sin(-pi/7)*cos(-6*pi/7))*cos(3903*pi/8),
{
field_simp at *,
},
have : sin(-pi) = sin(-6*pi/7) * cos(-pi/7) + sin(-pi/7) * cos(-6*pi/7),
{
have : sin(-pi) = sin((-6*pi/7) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = cos(3903*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/8) (244),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * cos(-pi/8) = sin(-7*pi/8) / 2 + sin(-9*pi/8) / 2,
{
rw sin_mul_cos,
have : sin((-pi) + (-pi/8)) = sin(-9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (-pi/8)) = sin(-7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_368 : 3*cos(1430*pi/9) - 4*cos(1430*pi/9)**3=cos(1745*pi/3):=
begin
have : (-3) * -cos(1430 * pi / 9) + 4 * (-cos(1430 * pi / 9)) ** 3 = 3*cos(1430*pi/9) - 4*cos(1430*pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -cos(1430*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/9) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/3) = cos(1745*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (291),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_369 : sin(5585*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(1161*pi/4) = sin(5585*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (1161*pi/4) (843),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(1161*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (145),
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


lemma Trigo_number_generalization_step2_370 : -sin(5207*pi/8)*cos(-pi/8) - sin(-pi/8)*cos(5207*pi/8)=- sqrt( 2 ) / 2:=
begin
have : -(sin(5207 * pi / 8) * cos(-pi / 8) + sin(-pi / 8) * cos(5207 * pi / 8)) = -sin(5207*pi/8)*cos(-pi/8) - sin(-pi/8)*cos(5207*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2603*pi/4) = sin(5207*pi/8) * cos(-pi/8) + sin(-pi/8) * cos(5207*pi/8),
{
have : sin(2603*pi/4) = sin((5207*pi/8) + (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(2603*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (325),
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


lemma Trigo_number_generalization_step2_371 : cos(2*pi/3)/2 + cos(4*pi/3)/2 - sin(-pi/3)*sin(pi)=- 1 / 2:=
begin
have : cos(4 * pi / 3) / 2 + cos(2 * pi / 3) / 2 - sin(-pi / 3) * sin(pi) = cos(2*pi/3)/2 + cos(4*pi/3)/2 - sin(-pi/3)*sin(pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * cos(-pi/3) = cos(4*pi/3) / 2 + cos(2*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (-pi/3)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (-pi/3)) = cos(4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(pi) * cos(-pi/3)) = cos(-pi/3)*cos(pi),
{
ring,
},
conv {to_lhs, rw this,},
have : -sin(-pi / 3) * sin(pi) + cos(-pi / 3) * cos(pi) = cos(-pi/3)*cos(pi) - sin(-pi/3)*sin(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(-pi/3) * sin(pi) + cos(-pi/3) * cos(pi),
{
have : cos(2*pi/3) = cos((-pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_372 (h0 : cos(-pi/7)≠ 0) : sin(-pi/7)/cos(-pi/7)=-cos(5819*pi/14)/cos(-pi/7):=
begin
have : tan(-pi/7) = sin(-pi/7) / cos(-pi/7),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = -cos(5819*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (207),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/7) = sin(-pi/7) / cos(-pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_373 : -sin(5729*pi/2)=- 1:=
begin
have : sin(2743*pi/2) = -sin(5729*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2743*pi/2) (746),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(2743*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (686),
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


lemma Trigo_number_generalization_step2_374 : cos(25905*pi/14)**2=sin(10329*pi/14)/2 + 1/2:=
begin
have : (-cos(25905 * pi / 14)) ** 2 = cos(25905*pi/14)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = -cos(25905*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/7) (925),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 - -sin(10329 * pi / 14) / 2 = sin(10329*pi/14)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/7) = -sin(10329*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/7) (368),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) ** 2 = 1 / 2 - cos(-2*pi/7) / 2,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
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


lemma Trigo_number_generalization_step2_375 (h0 : cos(-pi/12)≠ 0) (h1 : cos(-pi/4)≠ 0) (h2 : (1+tan(-pi/12)*tan(-pi/4))≠ 0) (h3 : (tan(-pi/4)*tan(-pi/12)+1)≠ 0) (h4 : cos(-pi/4)≠ 0) (h5 : cos(-pi/12)≠ 0) (h6 : tan((-pi/4)-(-pi/12))≠ 0) (h7 : 1+tan(-pi/4)*tan(-pi/12)≠ 0) (h8 : tan(-pi/6)≠ 0) (h9 : ((tan(-pi/4)-tan(-pi/12))/tan(-pi/6)-1+1)≠ 0) (h10 : (tan(-pi/4)-tan(-pi/12))≠ 0) : (tan(-pi/12) - tan(-pi/4))*tan(-pi/6)/(tan(-pi/4) - tan(-pi/12))=sqrt( 3 ) / 3:=
begin
have : (tan(-pi / 12) - tan(-pi / 4)) / ((tan(-pi / 4) - tan(-pi / 12)) / tan(-pi / 6) - 1 + 1) = (tan(-pi/12) - tan(-pi/4))*tan(-pi/6)/(tan(-pi/4) - tan(-pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) * tan(-pi/12) = ( tan(-pi/4) - tan(-pi/12) ) / tan(-pi/6) - 1,
{
rw tan_mul_tan,
have : tan((-pi/4) - (-pi/12)) = tan(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-pi/4) * tan(-pi/12)) = tan(-pi/4)*tan(-pi/12),
{
ring,
},
have : (tan(-pi / 12) - tan(-pi / 4)) / (1 + tan(-pi / 12) * tan(-pi / 4)) = (tan(-pi/12) - tan(-pi/4))/(tan(-pi/4)*tan(-pi/12) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(-pi/12) - tan(-pi/4) ) / ( 1 + tan(-pi/12) * tan(-pi/4) ),
{
have : tan(pi/6) = tan((-pi/12) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_376 : -1 + 2*sin(7001*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : -(1 - 2 * sin(7001 * pi / 12) ** 2) = -1 + 2*sin(7001*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7001*pi/6) = 1 - 2 * sin(7001*pi/12) ** 2,
{
have : cos(7001*pi/6) = cos(2*(7001*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(7001*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (583),
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


lemma Trigo_number_generalization_step2_377 (h0 : tan(1309*pi/4)≠ 0) (h1 : ((-1)/tan(2563*pi/4))≠ 0) (h2 : tan(2563*pi/4)≠ 0) : -tan(2563*pi/4)=1:=
begin
have : 1 / ((-1) / tan(2563 * pi / 4)) = -tan(2563*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1309*pi/4) = -1 / tan(2563*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (1309*pi/4) (313),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1 / tan(1309*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (327),
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


lemma Trigo_number_generalization_step2_378 : -cos(8923*pi/6)=sin(4634*pi/3):=
begin
have : cos(3265*pi/6) = -cos(8923*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3265*pi/6) (471),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(3265*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (272),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(4634*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (772),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_379 : -sin(20257*pi/7)=sin(8667*pi/7):=
begin
have : sin(12200*pi/7) = -sin(20257*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (12200*pi/7) (575),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(12200*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/7) (871),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(8667*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/7) (619),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_380 : 1 - 2*sin(-pi/14)**2=sin(18709*pi/14):=
begin
have : -sin(-pi / 14) ** 2 + (1 - sin(-pi / 14) ** 2) = 1 - 2*sin(-pi/14)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/14) ** 2 = 1 - sin(-pi/14) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = -sin(-pi/14) ** 2 + cos(-pi/14) ** 2,
{
have : cos(-pi/7) = cos(2*(-pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = sin(18709*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/7) (668),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_381 (h0 : tan(145*pi/2)≠ 0) (h1 : cos(143*pi/2)≠ 0) (h2 : cos(-pi)≠ 0) (h3 : (tan(143*pi/2)-tan(-pi))≠ 0) (h4 : ((tan(143*pi/2)-tan(-pi))/(1+tan(143*pi/2)*tan(-pi)))≠ 0) (h5 : (1+tan(143*pi/2)*tan(-pi))≠ 0) : -(tan(-pi)*tan(143*pi/2) + 1)/(tan(143*pi/2) - tan(-pi))=- tan(366*pi):=
begin
have : (-1) / ((tan(143 * pi / 2) - tan(-pi)) / (1 + tan(143 * pi / 2) * tan(-pi))) = -(tan(-pi)*tan(143*pi/2) + 1)/(tan(143*pi/2) - tan(-pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(145*pi/2) = ( tan(143*pi/2) - tan(-pi) ) / ( 1 + tan(143*pi/2) * tan(-pi) ),
{
have : tan(145*pi/2) = tan((143*pi/2) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(145 * pi / 2) = -1/tan(145*pi/2),
{
field_simp at *,
},
have : tan(2*pi) = -1 / tan(145*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - tan(366*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (368),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_382 : 1 - 2*cos(3499*pi/12)**2=cos(11987*pi/6):=
begin
have : 1 - 2 * (-cos(3499 * pi / 12)) ** 2 = 1 - 2*cos(3499*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = -cos(3499*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/12) (145),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(-pi/6) = cos(11987*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_383 (h0 : tan(1021*pi/2)≠ 0) (h1 : tan(-193*pi/2)≠ 0) (h2 : -tan((-193)*pi/2)≠ 0) : -1/tan(-193*pi/2)=tan(449*pi):=
begin
have : 1 / -tan((-193) * pi / 2) = -1/tan(-193*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1021*pi/2) = -tan(-193*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (1021*pi/2) (414),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(1021*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (511),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = tan(449*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (448),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_384 (h0 : tan(8435*pi/6)≠ 0) : -1/tan(8435*pi/6)=sqrt( 3 ):=
begin
have : (-1) / tan(8435 * pi / 6) = -1/tan(8435*pi/6),
{
field_simp at *,
},
have : tan(1324*pi/3) = -1 / tan(8435*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (1324*pi/3) (964),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(1324*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (441),
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


lemma Trigo_number_generalization_step2_385 : sin(-17159*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -sin((-17159) * pi / 12) = sin(-17159*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(23753*pi/12) = -sin(-17159*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (23753*pi/12) (274),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(23753*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (989),
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


lemma Trigo_number_generalization_step2_386 : (sin(-pi/7)*cos(59*pi/168) + sin(59*pi/168)*cos(-pi/7))*sin(pi/8) + cos(pi/8)*cos(5*pi/24)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi / 8) * (sin(59 * pi / 168) * cos(-pi / 7) + sin(-pi / 7) * cos(59 * pi / 168)) + cos(pi / 8) * cos(5 * pi / 24) = (sin(-pi/7)*cos(59*pi/168) + sin(59*pi/168)*cos(-pi/7))*sin(pi/8) + cos(pi/8)*cos(5*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/24) = sin(59*pi/168) * cos(-pi/7) + sin(-pi/7) * cos(59*pi/168),
{
have : sin(5*pi/24) = sin((59*pi/168) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 24) * sin(pi / 8) + cos(5 * pi / 24) * cos(pi / 8) = sin(pi/8)*sin(5*pi/24) + cos(pi/8)*cos(5*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(5*pi/24) * sin(pi/8) + cos(5*pi/24) * cos(pi/8),
{
have : cos(pi/12) = cos((5*pi/24) - (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_387 : -sin(-7176*pi/7)=- sin(10515*pi/7):=
begin
have : -sin((-7176) * pi / 7) = -sin(-7176*pi/7),
{
field_simp at *,
},
have : sin(7582*pi/7) = -sin(-7176*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (7582*pi/7) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = sin(7582*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/7) (541),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = - sin(10515*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/7) (751),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_388 (h0 : tan(5575*pi/6)≠ 0) : 1/tan(5575*pi/6)=sqrt( 3 ):=
begin
have : -((-1) / tan(5575 * pi / 6)) = 1/tan(5575*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(794*pi/3) = -1 / tan(5575*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (794*pi/3) (664),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = -tan(794*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (265),
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


lemma Trigo_number_generalization_step2_389 : 4*sin(1647*pi/7)**3 - 3*sin(1647*pi/7)=- sin(11073*pi/7):=
begin
have : -((-4) * sin(1647 * pi / 7) ** 3 + 3 * sin(1647 * pi / 7)) = 4*sin(1647*pi/7)**3 - 3*sin(1647*pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4941*pi/7) = -4 * sin(1647*pi/7) ** 3 + 3 * sin(1647*pi/7),
{
have : sin(4941*pi/7) = sin(3*(1647*pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = -sin(4941*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/7) (353),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = - sin(11073*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/7) (791),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_390 : cos(3830*pi/7)**2=1 - sin(6798*pi/7)**2:=
begin
have : 1 - (-sin(6798 * pi / 7)) ** 2 = 1 - sin(6798*pi/7)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = -sin(6798*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/7) (485),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-cos(3830 * pi / 7)) ** 2 = cos(3830*pi/7)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = -cos(3830*pi/7),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/7) (273),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) ** 2 = 1 - sin(pi/7) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_391 : cos(2*pi/3)=- 1 / 2:=
begin
have : 1 - 2 * (1 / 2 - cos(2 * pi / 3) / 2) = cos(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(2*pi/3) = 1 - 2 * sin(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_392 : (-sin(3717*pi/2)**2 + cos(pi/2)**2)*cos(pi/5)=cos(4*pi/5) / 2 + cos(6*pi/5) / 2:=
begin
have : sin(pi/2) = sin(3717*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (929),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi) * cos(pi/5) = cos(4*pi/5) / 2 + cos(6*pi/5) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (pi/5)) = cos(6*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (pi/5)) = cos(4*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_393 : -sin(37285*pi/21)=sin(pi/7)*cos(pi/3) + (sin(pi/9)*sin(16*pi/63) + cos(pi/9)*cos(16*pi/63))*sin(pi/3):=
begin
have : sin(10*pi/21) = -sin(37285*pi/21),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (10*pi/21) (887),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) * (sin(16 * pi / 63) * sin(pi / 9) + cos(16 * pi / 63) * cos(pi / 9)) + sin(pi / 7) * cos(pi / 3) = sin(pi/7)*cos(pi/3) + (sin(pi/9)*sin(16*pi/63) + cos(pi/9)*cos(16*pi/63))*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = sin(16*pi/63) * sin(pi/9) + cos(16*pi/63) * cos(pi/9),
{
have : cos(pi/7) = cos((16*pi/63) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(10*pi/21) = sin(pi/3) * cos(pi/7) + sin(pi/7) * cos(pi/3),
{
have : sin(10*pi/21) = sin((pi/3) + (pi/7)),
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


lemma Trigo_number_generalization_step2_394 : 1 - 2*sin(33697*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/24) = sin(33697*pi/24),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/24) (702),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = 1 - 2 * sin(pi/24) ** 2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_395 : sin(-33*pi/40)*cos(pi/8) + sin(7351*pi/8)*cos(-33*pi/40)=sin(-pi/5) * cos(-pi/2) + sin(-pi/2) * cos(-pi/5):=
begin
have : sin((-33) * pi / 40) * cos(pi / 8) + sin(7351 * pi / 8) * cos((-33) * pi / 40) = sin(-33*pi/40)*cos(pi/8) + sin(7351*pi/8)*cos(-33*pi/40),
{
field_simp at *,
},
have : sin(pi/8) = sin(7351*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/8) (459),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-33) * pi / 40) * cos(pi / 8) + sin(pi / 8) * cos((-33) * pi / 40) = sin(-33*pi/40)*cos(pi/8) + sin(pi/8)*cos(-33*pi/40),
{
field_simp at *,
},
have : sin(-7*pi/10) = sin(-33*pi/40) * cos(pi/8) + sin(pi/8) * cos(-33*pi/40),
{
have : sin(-7*pi/10) = sin((-33*pi/40) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/10) = sin(-pi/5) * cos(-pi/2) + sin(-pi/2) * cos(-pi/5),
{
have : sin(-7*pi/10) = sin((-pi/5) + (-pi/2)),
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


lemma Trigo_number_generalization_step2_396 : ((-3*cos(pi/4) + 4*cos(pi/4)**3)*cos(pi/4) - sin(pi/4)*sin(3*pi/4))**2=1 - sin(pi) ** 2:=
begin
have : (cos(pi / 4) * (4 * cos(pi / 4) ** 3 - 3 * cos(pi / 4)) - sin(pi / 4) * sin(3 * pi / 4)) ** 2 = ((-3*cos(pi/4) + 4*cos(pi/4)**3)*cos(pi/4) - sin(pi/4)*sin(3*pi/4))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = 4 * cos(pi/4) ** 3 - 3 * cos(pi/4),
{
have : cos(3*pi/4) = cos(3*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : (-sin(3 * pi / 4) * sin(pi / 4) + cos(3 * pi / 4) * cos(pi / 4)) ** 2 = (cos(pi/4)*cos(3*pi/4) - sin(pi/4)*sin(3*pi/4))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(3*pi/4) * sin(pi/4) + cos(3*pi/4) * cos(pi/4),
{
have : cos(pi) = cos((3*pi/4) + (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) ** 2 = 1 - sin(pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_397 : sin(5*pi/3)*cos(2*pi) - sin(2*pi)*cos(5*pi/3)=-sin(6601*pi/3):=
begin
have : sin(-pi/3) = sin(5*pi/3) * cos(2*pi) - sin(2*pi) * cos(5*pi/3),
{
have : sin(-pi/3) = sin((5*pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11783*pi/6) = sin(6601*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (11783*pi/6) (118),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = - cos(11783*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (981),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_398 : -sin(pi/9)*sin(17*pi/9) + cos(pi/9)*cos(17*pi/9)=cos(2894*pi):=
begin
have : -sin(17 * pi / 9) * sin(pi / 9) + cos(17 * pi / 9) * cos(pi / 9) = -sin(pi/9)*sin(17*pi/9) + cos(pi/9)*cos(17*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(17*pi/9) * sin(pi/9) + cos(17*pi/9) * cos(pi/9),
{
have : cos(2*pi) = cos((17*pi/9) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3413*pi/2) = cos(2894*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3413*pi/2) (593),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(3413*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (852),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_399 : 2*sin(pi/8)*cos(pi/8)=2*(-3*cos(pi/24) + 4*cos(pi/24)**3)*sin(pi/8):=
begin
have : sin(pi/4) = 2 * sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 8) * (4 * cos(pi / 24) ** 3 - 3 * cos(pi / 24)) = 2*(-3*cos(pi/24) + 4*cos(pi/24)**3)*sin(pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = 4 * cos(pi/24) ** 3 - 3 * cos(pi/24),
{
have : cos(pi/8) = cos(3*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) = 2 * sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_400 : cos(14255*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -cos(14255 * pi / 12) = cos(14255*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1955*pi/12) = -cos(14255*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (1955*pi/12) (512),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(1955*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (81),
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


lemma Trigo_number_generalization_step2_401 : sin(-pi/2)=(-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(-pi/3) - sin(-pi/6)*sin(3023*pi/6):=
begin
have : (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) * sin(-pi / 3) + sin(-pi / 6) * -sin(3023 * pi / 6) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(-pi/3) - sin(-pi/6)*sin(3023*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -sin(3023*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (251),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 6) * cos(-pi / 3) + sin(-pi / 3) * (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(-pi/3) + sin(-pi/6)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/12) ** 2 + cos(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = sin(-pi/6) * cos(-pi/3) + sin(-pi/3) * cos(-pi/6),
{
have : sin(-pi/2) = sin((-pi/6) + (-pi/3)),
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


lemma Trigo_number_generalization_step2_402 : (-sin(-pi/8)*sin(pi/4) + cos(-pi/8)*cos(pi/4))*sin(pi/7)=-sin(-pi/7)*cos(pi/8):=
begin
have : (-1) / 2 * (2 * sin(-pi / 7) * cos(pi / 8)) = -sin(-pi/7)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/56) - sin(15*pi/56) = 2 * sin(-pi/7) * cos(pi/8),
{
rw sin_sub_sin,
have : cos(((-pi/56) + (15*pi/56))/2) = cos(pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/56) - (15*pi/56))/2) = sin(-pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -1/2*(sin(-pi/56) - sin(15*pi/56)) = -sin(-pi/56)/2+sin(15*pi/56)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi / 7) * (-sin(-pi / 8) * sin(pi / 4) + cos(-pi / 8) * cos(pi / 4)) = (-sin(-pi/8)*sin(pi/4) + cos(-pi/8)*cos(pi/4))*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(-pi/8) * sin(pi/4) + cos(-pi/8) * cos(pi/4),
{
have : cos(pi/8) = cos((-pi/8) + (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) * cos(pi/8) = - sin(-pi/56) / 2 + sin(15*pi/56) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/8) + (pi/7)) = sin(15*pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (pi/7)) = sin(-pi/56),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_403 : 1 - 2*(-4*sin(pi/6)**3 + 3*sin(pi/6))**2=- 1:=
begin
have : 1 - 2 * ((-4) * sin(pi / 6) ** 3 + 3 * sin(pi / 6)) ** 2 = 1 - 2*(-4*sin(pi/6)**3 + 3*sin(pi/6))**2,
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
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_404 : -sin(pi/24)**2 + cos(pi/12)/2 + 1/2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -sin(pi / 24) ** 2 + (cos(pi / 12) / 2 + 1 / 2) = -sin(pi/24)**2 + cos(pi/12)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) ** 2 = cos(pi/12) / 2 + 1 / 2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(pi/24) ** 2 + cos(pi/24) ** 2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_405 : -4*sin(1538*pi/3)**3 + 3*sin(1538*pi/3)=- 4 * sin(pi) ** 3 + 3 * sin(pi):=
begin
have : (-4) * sin(1538 * pi / 3) ** 3 + 3 * sin(1538 * pi / 3) = -4*sin(1538*pi/3)**3 + 3*sin(1538*pi/3),
{
field_simp at *,
},
have : sin(1538*pi) = -4 * sin(1538*pi/3) ** 3 + 3 * sin(1538*pi/3),
{
have : sin(1538*pi) = sin(3*(1538*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) = sin(1538*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi) (770),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) = - 4 * sin(pi) ** 3 + 3 * sin(pi),
{
have : sin(3*pi) = sin(3*(pi)),
{
apply congr_arg,
ring,
},
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_406 : -sin(pi/16)**2 + cos(pi/16)**2=-sin(-pi/7)*cos(71357*pi/56) + sin(71357*pi/56)*cos(-pi/7):=
begin
have : cos(pi/8) = -sin(pi/16) ** 2 + cos(pi/16) ** 2,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(71357 * pi / 56) * cos(-pi / 7) - sin(-pi / 7) * cos(71357 * pi / 56) = -sin(-pi/7)*cos(71357*pi/56) + sin(71357*pi/56)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(10195*pi/8) = sin(71357*pi/56) * cos(-pi/7) - sin(-pi/7) * cos(71357*pi/56),
{
have : sin(10195*pi/8) = sin((71357*pi/56) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = sin(10195*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/8) (637),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_407 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : (cos(2*pi/3)+1)≠ 0) (h2 : (1+cos(2*pi/3))≠ 0) : -cos(7483*pi/6)/(cos(2*pi/3) + 1)=sqrt( 3 ):=
begin
have : sin(2*pi/3) = -cos(7483*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (623),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_408 : -2*sin(-pi/2)*cos(-pi/2) + cos(7489*pi/6)=2 * sin(2*pi/3) * cos(-pi/3):=
begin
have : (-2) * sin(-pi / 2) * cos(-pi / 2) + cos(7489 * pi / 6) = -2*sin(-pi/2)*cos(-pi/2) + cos(7489*pi/6),
{
field_simp at *,
},
have : sin(pi/3) = cos(7489*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (624),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) - 2 * sin(-pi / 2) * cos(-pi / 2) = -2*sin(-pi/2)*cos(-pi/2) + sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/3) - sin(-pi) = 2 * sin(2*pi/3) * cos(-pi/3),
{
rw sin_sub_sin,
have : cos(((pi/3) + (-pi))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (-pi))/2) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_409 : -cos(7160*pi/7)=cos(1835*pi/7):=
begin
have : cos(5720*pi/7) = cos(7160*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5720*pi/7) (920),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = -cos(5720*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/7) (408),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = cos(1835*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/7) (131),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_410 : cos(-2*pi/5)=1 - 2*cos(2053*pi/10)**2:=
begin
have : sin(-pi/5) = cos(2053*pi/10),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (102),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -sin(-pi / 5) ** 2 + (1 - sin(-pi / 5) ** 2) = 1 - 2*sin(-pi/5)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) ** 2 = 1 - sin(-pi/5) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/5) = - sin(-pi/5) ** 2 + cos(-pi/5) ** 2,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
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


lemma Trigo_number_generalization_step2_411 : -sin(-2525*pi/3)=sin(4072*pi/3):=
begin
have : -sin((-2525) * pi / 3) = -sin(-2525*pi/3),
{
field_simp at *,
},
have : sin(3257*pi/3) = -sin(-2525*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (3257*pi/3) (122),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(3257*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (543),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(4072*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (678),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_412 (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/12)**2-1)≠ 0) (h2 : (-1+2*cos(pi/12)**2)≠ 0) : sin(pi/6)/(-1 + 2*cos(pi/12)**2)=sqrt( 3 ) / 3:=
begin
have : sin(pi / 6) / (2 * cos(pi / 12) ** 2 - 1) = sin(pi/6)/(-1 + 2*cos(pi/12)**2),
{
field_simp at *,
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
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_413 (h0 : cos(-pi/8)≠ 0) (h1 : (4*cos(-pi/8)**2)≠ 0) (h2 : (2*cos(-pi/8))≠ 0) (h3 : (4*(-cos(12711*pi/8))**2)≠ 0) (h4 : (4*cos(12711*pi/8)**2)≠ 0) : sin(-pi/4)**2/(4*cos(12711*pi/8)**2)=1 - cos(-pi/8) ** 2:=
begin
have : sin(-pi / 4) ** 2 / (4 * (-cos(12711 * pi / 8)) ** 2) = sin(-pi/4)**2/(4*cos(12711*pi/8)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = -cos(12711*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/8) (794),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi / 4) / (2 * cos(-pi / 8))) ** 2 = sin(-pi/4)**2/(4*cos(-pi/8)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(-pi/4) / ( 2 * cos(-pi/8) ),
{
have : sin(-pi/4) = sin(2*(-pi/8)),
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
have : sin(-pi/8) ** 2 = 1 - cos(-pi/8) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_414 : -sin(-609*pi/4)=sqrt( 2 ) / 2:=
begin
have : -sin((-609) * pi / 4) = -sin(-609*pi/4),
{
field_simp at *,
},
have : sin(4521*pi/4) = -sin(-609*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (4521*pi/4) (489),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(4521*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (565),
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


lemma Trigo_number_generalization_step2_415 (h0 : cos(pi/2)≠ 0) (h1 : (1-tan(pi/2)**2)≠ 0) (h2 : cos((pi)/2)≠ 0) (h3 : (1-((1-cos(pi))/sin(pi))**2)≠ 0) (h4 : sin(pi)≠ 0) (h5 : ((-(1-cos(pi))**2/sin(pi)**2+1)*sin(pi))≠ 0) : 2*(1 - cos(pi))/((-(1 - cos(pi))**2/sin(pi)**2 + 1)*sin(pi))=- 1 / tan(1967*pi/2):=
begin
have : 2 * ((1 - cos(pi)) / sin(pi)) / (1 - ((1 - cos(pi)) / sin(pi)) ** 2) = 2*(1 - cos(pi))/((-(1 - cos(pi))**2/sin(pi)**2 + 1)*sin(pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi) = 2 * tan(pi/2) / ( 1 - tan(pi/2) ** 2 ),
{
have : tan(pi) = tan(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(1967*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (982),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_416 : -2*sin(745*pi)*cos(745*pi)=- 4 * sin(pi) ** 3 + 3 * sin(pi):=
begin
have : -(2 * sin(745 * pi) * cos(745 * pi)) = -2*sin(745*pi)*cos(745*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1490*pi) = 2 * sin(745*pi) * cos(745*pi),
{
have : sin(1490*pi) = sin(2*(745*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) = -sin(1490*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3*pi) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) = - 4 * sin(pi) ** 3 + 3 * sin(pi),
{
have : sin(3*pi) = sin(3*(pi)),
{
apply congr_arg,
ring,
},
rw sin_three_mul,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_417 : sin(6565*pi/4)*cos(pi/3)=- sin(7*pi/12) / 2 + sin(pi/12) / 2:=
begin
have : sin(1957*pi/4) = sin(6565*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (1957*pi/4) (576),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(1957*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/4) (244),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * cos(pi/3) = - sin(7*pi/12) / 2 + sin(pi/12) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/4)) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/4)) = sin(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_418 : -sin(4025*pi/8)*cos(7*pi/8) + sin(7*pi/8)*cos(-pi/8)=cos(1425*pi/2):=
begin
have : sin(-pi/8) = sin(4025*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/8) (251),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 8) * cos(-pi / 8) - sin(-pi / 8) * cos(7 * pi / 8) = -sin(-pi/8)*cos(7*pi/8) + sin(7*pi/8)*cos(-pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(7*pi/8) * cos(-pi/8) - sin(-pi/8) * cos(7*pi/8),
{
have : sin(pi) = sin((7*pi/8) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(1425*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (355),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_419 (h0 : (-1+2*cos(pi/18)**2)≠ 0) (h1 : (2*cos(pi/18)**2-1)≠ 0) (h2 : (-1+2*(sin(7*pi/18)*sin(pi/3)+cos(7*pi/18)*cos(pi/3))**2)≠ 0) (h3 : (-1+2*(cos(pi/3)*cos(7*pi/18)+sin(pi/3)*sin(7*pi/18))**2)≠ 0) : tan(pi/9)=sin(pi/9)/(-1 + 2*(cos(pi/3)*cos(7*pi/18) + sin(pi/3)*sin(7*pi/18))**2):=
begin
have : sin(pi / 9) / (-1 + 2 * (sin(7 * pi / 18) * sin(pi / 3) + cos(7 * pi / 18) * cos(pi / 3)) ** 2) = sin(pi/9)/(-1 + 2*(cos(pi/3)*cos(7*pi/18) + sin(pi/3)*sin(7*pi/18))**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/18) = sin(7*pi/18) * sin(pi/3) + cos(7*pi/18) * cos(pi/3),
{
have : cos(pi/18) = cos((7*pi/18) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 9) / (2 * cos(pi / 18) ** 2 - 1) = sin(pi/9)/(-1 + 2*cos(pi/18)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) = 2 * cos(pi/18) ** 2 - 1,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : tan(pi/9) = sin(pi/9) / cos(pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_420 (h0 : sin(10321*pi/18)≠ 0) (h1 : (2*sin(10321*pi/18))≠ 0) : -cos(4475*pi/18)=-sin(10321*pi/9)/(2*sin(10321*pi/18)):=
begin
have : sin(pi/9) = -cos(4475*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/9) (124),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(10321 * pi / 9) / (2 * sin(10321 * pi / 18))) = -sin(10321*pi/9)/(2*sin(10321*pi/18)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(10321*pi/18) = sin(10321*pi/9) / ( 2 * sin(10321*pi/18) ),
{
have : sin(10321*pi/9) = sin(2*(10321*pi/18)),
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
have : sin(pi/9) = - cos(10321*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (286),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_421 (h0 : cos((5111*pi/6)/2)≠ 0) (h1 : sin(5111*pi/6)≠ 0) : -(1 - cos(5111*pi/6))/sin(5111*pi/6)=2 - sqrt( 3 ):=
begin
have : -((1 - cos(5111 * pi / 6)) / sin(5111 * pi / 6)) = -(1 - cos(5111*pi/6))/sin(5111*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(5111*pi/12) = ( 1 - cos(5111*pi/6) ) / sin(5111*pi/6),
{
have : tan(5111*pi/12) = tan((5111*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(5111*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (426),
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


lemma Trigo_number_generalization_step2_422 : cos(pi)*cos(2867*pi/2) + sin(pi)*sin(2867*pi/2)=0:=
begin
have : sin(2867 * pi / 2) * sin(pi) + cos(2867 * pi / 2) * cos(pi) = cos(pi)*cos(2867*pi/2) + sin(pi)*sin(2867*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2865*pi/2) = sin(2867*pi/2) * sin(pi) + cos(2867*pi/2) * cos(pi),
{
have : cos(2865*pi/2) = cos((2867*pi/2) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(2865*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (715),
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


lemma Trigo_number_generalization_step2_423 : sin(6*pi/7)=-sin(pi)*cos(1476*pi/7) - (1 - 2*sin(pi/2)**2)*sin(pi/7):=
begin
have : sin(pi) * -cos(1476 * pi / 7) - (1 - 2 * sin(pi / 2) ** 2) * sin(pi / 7) = -sin(pi)*cos(1476*pi/7) - (1 - 2*sin(pi/2)**2)*sin(pi/7),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = -cos(1476*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/7) (105),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * cos(pi / 7) - sin(pi / 7) * (1 - 2 * sin(pi / 2) ** 2) = sin(pi)*cos(pi/7) - (1 - 2*sin(pi/2)**2)*sin(pi/7),
{
field_simp at *,
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
conv {to_rhs, rw ← this,},
have : sin(6*pi/7) = sin(pi) * cos(pi/7) - sin(pi/7) * cos(pi),
{
have : sin(6*pi/7) = sin((pi) - (pi/7)),
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


lemma Trigo_number_generalization_step2_424 (h0 : tan(4363*pi/8)≠ 0) (h1 : cos((4363*pi/4)/2)≠ 0) (h2 : ((1-cos(4363*pi/4))/sin(4363*pi/4))≠ 0) (h3 : (1-cos(4363*pi/4))≠ 0) (h4 : sin(4363*pi/4)≠ 0) : sin(4363*pi/4)/(1 - cos(4363*pi/4))=- 1 / tan(2157*pi/8):=
begin
have : 1 / ((1 - cos(4363 * pi / 4)) / sin(4363 * pi / 4)) = sin(4363*pi/4)/(1 - cos(4363*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(4363*pi/8) = ( 1 - cos(4363*pi/4) ) / sin(4363*pi/4),
{
have : tan(4363*pi/8) = tan((4363*pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = 1 / tan(4363*pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/8) (545),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = - 1 / tan(2157*pi/8),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/8) (269),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_425 (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : cos(1130*pi/3)=sin(-pi/3)*cos(pi/6) + sin(pi/3)*cos(-pi/3)/(2*cos(pi/6)):=
begin
have : sin(-pi / 3) * cos(pi / 6) + sin(pi / 3) / (2 * cos(pi / 6)) * cos(-pi / 3) = sin(-pi/3)*cos(pi/6) + sin(pi/3)*cos(-pi/3)/(2*cos(pi/6)),
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
have : sin(-pi/6) = cos(1130*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (188),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(-pi/3) * cos(pi/6) + sin(pi/6) * cos(-pi/3),
{
have : sin(-pi/6) = sin((-pi/3) + (pi/6)),
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


lemma Trigo_number_generalization_step2_426 : -sin(15517*pi/10)=-3*cos(3119*pi/15) + 4*cos(3119*pi/15)**3:=
begin
have : 4 * cos(3119 * pi / 15) ** 3 - 3 * cos(3119 * pi / 15) = -3*cos(3119*pi/15) + 4*cos(3119*pi/15)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3119*pi/5) = 4 * cos(3119*pi/15) ** 3 - 3 * cos(3119*pi/15),
{
have : cos(3119*pi/5) = cos(3*(3119*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = -sin(15517*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (775),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = cos(3119*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/5) (312),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_427 : -sin(1045*pi/3)=- sin(1184*pi/3):=
begin
have : sin(2558*pi/3) = sin(1045*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2558*pi/3) (600),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(2558*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (426),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(1184*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (197),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_428 : 2*sin(2183*pi/4)*cos(2183*pi/4)=- 1:=
begin
have : sin(2183*pi/2) = 2 * sin(2183*pi/4) * cos(2183*pi/4),
{
have : sin(2183*pi/2) = sin(2*(2183*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(2183*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (545),
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


lemma Trigo_number_generalization_step2_429 : 3*sin(-pi/9) - 4*sin(-pi/9)**3=2*(-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(-pi/6):=
begin
have : 2 * sin(-pi / 6) * (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) = 2*(-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(-pi/6),
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/12) ** 2 + cos(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_430 (h0 : cos(9143*pi/7)≠ 0) (h1 : tan(4387*pi/14)≠ 0) : -1/tan(4387*pi/14)=sin(-pi/7)/cos(9143*pi/7):=
begin
have : (-1) / tan(4387 * pi / 14) = -1/tan(4387*pi/14),
{
field_simp at *,
},
have : tan(-pi/7) = -1 / tan(4387*pi/14),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/7) (313),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = cos(9143*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/7) (653),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/7) = sin(-pi/7) / cos(-pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_431 : -cos(1586*pi/3)**2 + cos(pi/6)**2=2 * cos(pi/6) ** 2 - 1:=
begin
have : -(-cos(1586 * pi / 3)) ** 2 + cos(pi / 6) ** 2 = -cos(1586*pi/3)**2 + cos(pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(1586*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (264),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_432 (h0 : cos(-pi/7)≠ 0) : cos(34225*pi/14)/cos(-pi/7)=tan(-pi/7):=
begin
have : - -cos(34225 * pi / 14) / cos(-pi / 7) = cos(34225*pi/14)/cos(-pi/7),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(6707*pi/7) = -cos(34225*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (6707*pi/7) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = -sin(6707*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/7) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) / cos(-pi/7) = tan(-pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_433 : -(1 - 2*sin(-pi/10)**2)*cos(874*pi/3)=cos(2*pi/15) / 2 + cos(-8*pi/15) / 2:=
begin
have : (1 - 2 * sin(-pi / 10) ** 2) * -cos(874 * pi / 3) = -(1 - 2*sin(-pi/10)**2)*cos(874*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(874*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (145),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = 1 - 2 * sin(-pi/10) ** 2,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) * cos(-pi/3) = cos(2*pi/15) / 2 + cos(-8*pi/15) / 2,
{
rw cos_mul_cos,
have : cos((-pi/5) + (-pi/3)) = cos(-8*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (-pi/3)) = cos(2*pi/15),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_434 : (sin(pi/3)*sin(2*pi) + cos(pi/3)*cos(2*pi))*sin(-pi) + sin(5*pi/3)*cos(-pi)=sqrt( 3 ) / 2:=
begin
have : sin(-pi) * (sin(2 * pi) * sin(pi / 3) + cos(2 * pi) * cos(pi / 3)) + sin(5 * pi / 3) * cos(-pi) = (sin(pi/3)*sin(2*pi) + cos(pi/3)*cos(2*pi))*sin(-pi) + sin(5*pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/3) = sin(2*pi) * sin(pi/3) + cos(2*pi) * cos(pi/3),
{
have : cos(5*pi/3) = cos((2*pi) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 3) * cos(-pi) + sin(-pi) * cos(5 * pi / 3) = sin(-pi)*cos(5*pi/3) + sin(5*pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(5*pi/3) * cos(-pi) + sin(-pi) * cos(5*pi/3),
{
have : sin(2*pi/3) = sin((5*pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_435 : (1 - 2*sin(pi/2)**2)*sin(4891*pi/4)=- sin(3*pi/4) / 2 + sin(5*pi/4) / 2:=
begin
have : sin(4891 * pi / 4) * (1 - 2 * sin(pi / 2) ** 2) = (1 - 2*sin(pi/2)**2)*sin(4891*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(4891*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (611),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) * cos(pi) = - sin(3*pi/4) / 2 + sin(5*pi/4) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi) + (pi/4)) = sin(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi/4)) = sin(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_436 : -1 + 2*cos(3559*pi/6)**2=1 / 2:=
begin
have : 2 * cos(3559 * pi / 6) ** 2 - 1 = -1 + 2*cos(3559*pi/6)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3559*pi/3) = 2 * cos(3559*pi/6) ** 2 - 1,
{
have : cos(3559*pi/3) = cos(2*(3559*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(3559*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (593),
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


lemma Trigo_number_generalization_step2_437 : -sin(3821*pi/2)*cos(2*pi) + sin(-pi)*sin(2*pi)=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : cos(-pi) = -sin(3821*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (955),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) * sin(-pi) + cos(2 * pi) * cos(-pi) = cos(-pi)*cos(2*pi) + sin(-pi)*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = sin(2*pi) * sin(-pi) + cos(2*pi) * cos(-pi),
{
have : cos(3*pi) = cos((2*pi) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = 4 * cos(pi) ** 3 - 3 * cos(pi),
{
have : cos(3*pi) = cos(3*(pi)),
{
apply congr_arg,
ring,
},
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_438 : -2*sin(3*pi/16)*cos(23283*pi/16)=- 4 * sin(pi/8) ** 3 + 3 * sin(pi/8):=
begin
have : 2 * sin(3 * pi / 16) * -cos(23283 * pi / 16) = -2*sin(3*pi/16)*cos(23283*pi/16),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/16) = -cos(23283*pi/16),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3*pi/16) (727),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/8) = 2 * sin(3*pi/16) * cos(3*pi/16),
{
have : sin(3*pi/8) = sin(2*(3*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/8) = - 4 * sin(pi/8) ** 3 + 3 * sin(pi/8),
{
have : sin(3*pi/8) = sin(3*(pi/8)),
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


lemma Trigo_number_generalization_step2_439 (h0 : cos((-2*pi/5)/2)≠ 0) (h1 : (cos(-2*pi/5)+1)≠ 0) (h2 : (1+cos((-2)*pi/5))≠ 0) (h3 : cos(5399*pi/20)≠ 0) (h4 : cos(-pi/4)≠ 0) (h5 : (tan(-pi/4)*tan(5399*pi/20)+1)≠ 0) (h6 : (1+tan(5399*pi/20)*tan(-pi/4))≠ 0) : sin(-2*pi/5)/(cos(-2*pi/5) + 1)=-(tan(5399*pi/20) - tan(-pi/4))/(tan(-pi/4)*tan(5399*pi/20) + 1):=
begin
have : -((tan(5399 * pi / 20) - tan(-pi / 4)) / (1 + tan(5399 * pi / 20) * tan(-pi / 4))) = -(tan(5399*pi/20) - tan(-pi/4))/(tan(-pi/4)*tan(5399*pi/20) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : tan(1351*pi/5) = ( tan(5399*pi/20) - tan(-pi/4) ) / ( 1 + tan(5399*pi/20) * tan(-pi/4) ),
{
have : tan(1351*pi/5) = tan((5399*pi/20) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin((-2) * pi / 5) / (1 + cos((-2) * pi / 5)) = sin(-2*pi/5)/(cos(-2*pi/5) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = sin(-2*pi/5) / ( 1 + cos(-2*pi/5) ),
{
have : tan(-pi/5) = tan((-2*pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = - tan(1351*pi/5),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/5) (270),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_440 (h0 : cos(-7*pi/16)≠ 0) (h1 : (2*cos((-7)*pi/16))≠ 0) (h2 : (2*cos(-7*pi/16)**2)≠ 0) : -sin(-7*pi/8)**2/(2*cos(-7*pi/16)**2) + 1=- sin(pi/8) * sin(-pi) + cos(pi/8) * cos(-pi):=
begin
have : 1 - 2 * (sin((-7) * pi / 8) / (2 * cos((-7) * pi / 16))) ** 2 = -sin(-7*pi/8)**2/(2*cos(-7*pi/16)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/16) = sin(-7*pi/8) / ( 2 * cos(-7*pi/16) ),
{
have : sin(-7*pi/8) = sin(2*(-7*pi/16)),
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
have : 1 - 2 * sin((-7) * pi / 16) ** 2 = 1 - 2*sin(-7*pi/16)**2,
{
field_simp at *,
},
have : cos(-7*pi/8) = 1 - 2 * sin(-7*pi/16) ** 2,
{
have : cos(-7*pi/8) = cos(2*(-7*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/8) = - sin(pi/8) * sin(-pi) + cos(pi/8) * cos(-pi),
{
have : cos(-7*pi/8) = cos((pi/8) + (-pi)),
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


lemma Trigo_number_generalization_step2_441 : -(-4*sin(pi/6)**3 + 3*sin(pi/6))*cos(-5*pi/2) + sin(-5*pi/2)*cos(pi/2)=- 4 * sin(-pi) ** 3 + 3 * sin(-pi):=
begin
have : -((-4) * sin(pi / 6) ** 3 + 3 * sin(pi / 6)) * cos((-5) * pi / 2) + sin((-5) * pi / 2) * cos(pi / 2) = -(-4*sin(pi/6)**3 + 3*sin(pi/6))*cos(-5*pi/2) + sin(-5*pi/2)*cos(pi/2),
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
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 2) * cos(pi / 2) - sin(pi / 2) * cos((-5) * pi / 2) = -sin(pi/2)*cos(-5*pi/2) + sin(-5*pi/2)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi) = sin(-5*pi/2) * cos(pi/2) - sin(pi/2) * cos(-5*pi/2),
{
have : sin(-3*pi) = sin((-5*pi/2) - (pi/2)),
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


lemma Trigo_number_generalization_step2_442 (h0 : sin(-pi/4)≠ 0) (h1 : (2*sin(-pi/4))≠ 0) : sin(-pi/4)*cos(pi/8) + sin(-pi/2)*sin(pi/8)/(2*sin(-pi/4))=cos(8373*pi/8):=
begin
have : sin(-pi / 4) * cos(pi / 8) + sin(pi / 8) * (sin(-pi / 2) / (2 * sin(-pi / 4))) = sin(-pi/4)*cos(pi/8) + sin(-pi/2)*sin(pi/8)/(2*sin(-pi/4)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(-pi/2) / ( 2 * sin(-pi/4) ),
{
have : sin(-pi/2) = sin(2*(-pi/4)),
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
have : sin(-pi/8) = sin(-pi/4) * cos(pi/8) + sin(pi/8) * cos(-pi/4),
{
have : sin(-pi/8) = sin((-pi/4) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = cos(8373*pi/8),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/8) (523),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_443 : -cos(363*pi)=-cos(2189*pi):=
begin
have : cos(2*pi) = -cos(363*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (182),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1403*pi/2) = cos(2189*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1403*pi/2) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(1403*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (349),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_444 (h0 : cos(-23*pi/12)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (1+tan((-23)*pi/12)*tan((-2)*pi))≠ 0) (h3 : (tan(-2*pi)*tan(-23*pi/12)+1)≠ 0) (h4 : cos(-23*pi/12)≠ 0) (h5 : cos(-2*pi)≠ 0) (h6 : ((tan(-2*pi)*tan(-23*pi/12)+1)*cos(-2*pi)*cos(-23*pi/12))≠ 0) (h7 : (cos((-23)*pi/12)*cos((-2)*pi))≠ 0) (h8 : (tan((-2)*pi)*tan((-23)*pi/12)+1)≠ 0) : sin(pi/12)/((tan(-2*pi)*tan(-23*pi/12) + 1)*cos(-2*pi)*cos(-23*pi/12))=2 - sqrt( 3 ):=
begin
have : sin(pi / 12) / (cos((-23) * pi / 12) * cos((-2) * pi)) / (tan((-2) * pi) * tan((-23) * pi / 12) + 1) = sin(pi/12)/((tan(-2*pi)*tan(-23*pi/12) + 1)*cos(-2*pi)*cos(-23*pi/12)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-23*pi/12) - tan(-2*pi) = sin(pi/12) / ( cos(-23*pi/12) * cos(-2*pi) ),
{
rw tan_sub_tan',
have : sin((-23*pi/12) - (-2*pi)) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-23*pi/12) - tan(-2*pi)) = (-tan(-2*pi)+tan(-23*pi/12)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan((-23) * pi / 12) - tan((-2) * pi)) / (1 + tan((-23) * pi / 12) * tan((-2) * pi)) = (-tan(-2*pi) + tan(-23*pi/12))/(tan(-2*pi)*tan(-23*pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(-23*pi/12) - tan(-2*pi) ) / ( 1 + tan(-23*pi/12) * tan(-2*pi) ),
{
have : tan(pi/12) = tan((-23*pi/12) - (-2*pi)),
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


lemma Trigo_number_generalization_step2_445 : cos(7*pi/8)*cos(3885*pi/8) + sin(7*pi/8)*cos(-pi/8)=2 * sin(pi/2) * cos(pi/2):=
begin
have : - -cos(3885 * pi / 8) * cos(7 * pi / 8) + sin(7 * pi / 8) * cos(-pi / 8) = cos(7*pi/8)*cos(3885*pi/8) + sin(7*pi/8)*cos(-pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -cos(3885*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (242),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 8) * cos(-pi / 8) - sin(-pi / 8) * cos(7 * pi / 8) = -sin(-pi/8)*cos(7*pi/8) + sin(7*pi/8)*cos(-pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(7*pi/8) * cos(-pi/8) - sin(-pi/8) * cos(7*pi/8),
{
have : sin(pi) = sin((7*pi/8) - (-pi/8)),
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


lemma Trigo_number_generalization_step2_446 : 3*sin(-pi/6) - 4*sin(-pi/6)**3=-sin(3065*pi/2):=
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
have : cos(46*pi) = sin(3065*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (46*pi) (789),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = - cos(46*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_447 : sin(3*pi/2)*sin(2*pi) - sin(1610*pi)*cos(2*pi)=2 * cos(-pi/4) ** 2 - 1:=
begin
have : -sin(1610 * pi) * cos(2 * pi) + sin(3 * pi / 2) * sin(2 * pi) = sin(3*pi/2)*sin(2*pi) - sin(1610*pi)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/2) = -sin(1610*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/2) (805),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3 * pi / 2) * sin(2 * pi) + cos(3 * pi / 2) * cos(2 * pi) = cos(3*pi/2)*cos(2*pi) + sin(3*pi/2)*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(3*pi/2) * sin(2*pi) + cos(3*pi/2) * cos(2*pi),
{
have : cos(-pi/2) = cos((3*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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
rw this,
end


lemma Trigo_number_generalization_step2_448 : sin(-pi)=sin(-845*pi):=
begin
have : - -sin((-845) * pi) = sin(-845*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3661*pi/2) = -sin(-845*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3661*pi/2) (492),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(1057*pi/2) = cos(3661*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (1057*pi/2) (651),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(1057*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_449 (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : cos(-2*pi)*cos(-3*pi/2) + sin(-2*pi)*sin(-3*pi/2)=-cos(2737*pi/2)/(2*sin(pi/2)):=
begin
have : sin((-3) * pi / 2) * sin((-2) * pi) + cos((-3) * pi / 2) * cos((-2) * pi) = cos(-2*pi)*cos(-3*pi/2) + sin(-2*pi)*sin(-3*pi/2),
{
field_simp at *,
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
have : sin(pi) = -cos(2737*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (684),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_450 (h0 : tan(4737*pi/10)≠ 0) (h1 : cos((4737*pi/5)/2)≠ 0) (h2 : (1+cos(4737*pi/5))≠ 0) (h3 : (sin(4737*pi/5)/(1+cos(4737*pi/5)))≠ 0) (h4 : sin(4737*pi/5)≠ 0) : -(cos(4737*pi/5) + 1)/sin(4737*pi/5)=1 / tan(8973*pi/10):=
begin
have : (-1) / (sin(4737 * pi / 5) / (1 + cos(4737 * pi / 5))) = -(cos(4737*pi/5) + 1)/sin(4737*pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(4737*pi/10) = sin(4737*pi/5) / ( 1 + cos(4737*pi/5) ),
{
have : tan(4737*pi/10) = tan((4737*pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(4737 * pi / 10) = -1/tan(4737*pi/10),
{
field_simp at *,
},
have : tan(pi/5) = -1 / tan(4737*pi/10),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/5) (473),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/5) = 1 / tan(8973*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/5) (897),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_451 (h0 : sin(pi/7)≠ 0) (h1 : (2*sin(pi/7))≠ 0) : sin(2*pi/63)=sin(-pi/9)*sin(2*pi/7)/(2*sin(pi/7)) + (-1 + 2*cos(-pi/18)**2)*sin(pi/7):=
begin
have : sin(-pi / 9) * (sin(2 * pi / 7) / (2 * sin(pi / 7))) + (-1 + 2 * cos(-pi / 18) ** 2) * sin(pi / 7) = sin(-pi/9)*sin(2*pi/7)/(2*sin(pi/7)) + (-1 + 2*cos(-pi/18)**2)*sin(pi/7),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = sin(2*pi/7) / ( 2 * sin(pi/7) ),
{
have : sin(2*pi/7) = sin(2*(pi/7)),
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
have : sin(-pi / 9) * cos(pi / 7) + sin(pi / 7) * (2 * cos(-pi / 18) ** 2 - 1) = sin(-pi/9)*cos(pi/7) + (-1 + 2*cos(-pi/18)**2)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = 2 * cos(-pi/18) ** 2 - 1,
{
have : cos(-pi/9) = cos(2*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/63) = sin(-pi/9) * cos(pi/7) + sin(pi/7) * cos(-pi/9),
{
have : sin(2*pi/63) = sin((-pi/9) + (pi/7)),
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


lemma Trigo_number_generalization_step2_452 (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) (h2 : (1-tan(9277*pi/12)**2)≠ 0) : 2*tan(9277*pi/12)/(1 - tan(9277*pi/12)**2)=sqrt( 3 ) / 3:=
begin
have : tan(pi/12) = tan(9277*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (773),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_453 (h0 : cos(5639*pi/6)≠ 0) (h1 : (2*cos(5639*pi/6))≠ 0) : -sin(5639*pi/3)/(2*cos(5639*pi/6))=1 / 2:=
begin
have : -(sin(5639 * pi / 3) / (2 * cos(5639 * pi / 6))) = -sin(5639*pi/3)/(2*cos(5639*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5639*pi/6) = sin(5639*pi/3) / ( 2 * cos(5639*pi/6) ),
{
have : sin(5639*pi/3) = sin(2*(5639*pi/6)),
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
have : sin(pi/6) = -sin(5639*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (470),
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


lemma Trigo_number_generalization_step2_454 : sin(15299*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(6323*pi/12) = sin(15299*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (6323*pi/12) (374),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(6323*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (263),
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


lemma Trigo_number_generalization_step2_455 : sin(11*pi/6)/2 - cos(3122*pi/3)/2=sin(13*pi/6) / 2 + sin(11*pi/6) / 2:=
begin
have : sin(-13*pi/6) = cos(3122*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-13*pi/6) (519),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-13) * pi / 6) / 2 + sin(11 * pi / 6) / 2 = sin(11*pi/6)/2 - sin(-13*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(-pi/6) = -sin(-13*pi/6) / 2 + sin(11*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/6) + (2*pi)) = sin(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (2*pi)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(2*pi) * cos(-pi/6)) = sin(2*pi)*cos(-pi/6),
{
ring,
},
have : sin(2*pi) * cos(-pi/6) = sin(13*pi/6) / 2 + sin(11*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((2*pi) + (-pi/6)) = sin(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (-pi/6)) = sin(13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_456 : -3*cos(3133*pi/18) + 4*cos(3133*pi/18)**3=cos(5161*pi/6):=
begin
have : 4 * cos(3133 * pi / 18) ** 3 - 3 * cos(3133 * pi / 18) = -3*cos(3133*pi/18) + 4*cos(3133*pi/18)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3133*pi/6) = 4 * cos(3133*pi/18) ** 3 - 3 * cos(3133*pi/18),
{
have : cos(3133*pi/6) = cos(3*(3133*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(3133*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (261),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(5161*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (430),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_457 : -4*(sin(pi/9)*cos(pi/6) + sin(pi/6)*cos(pi/9))**3 + 3*sin(pi/9)*cos(pi/6) + 3*sin(pi/6)*cos(pi/9)=1 / 2:=
begin
have : (-4) * (sin(pi / 6) * cos(pi / 9) + sin(pi / 9) * cos(pi / 6)) ** 3 + 3 * (sin(pi / 6) * cos(pi / 9) + sin(pi / 9) * cos(pi / 6)) = -4*(sin(pi/9)*cos(pi/6) + sin(pi/6)*cos(pi/9))**3 + 3*sin(pi/9)*cos(pi/6) + 3*sin(pi/6)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = sin(pi/6) * cos(pi/9) + sin(pi/9) * cos(pi/6),
{
have : sin(5*pi/18) = sin((pi/6) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(5 * pi / 18) ** 3 + 3 * sin(5 * pi / 18) = -4*sin(5*pi/18)**3 + 3*sin(5*pi/18),
{
field_simp at *,
},
have : sin(5*pi/6) = -4 * sin(5*pi/18) ** 3 + 3 * sin(5*pi/18),
{
have : sin(5*pi/6) = sin(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_458 : (1 - 2*sin(pi/10)**2)**2=1 - cos(19213*pi/10)**2:=
begin
have : cos(pi/5) = 1 - 2 * sin(pi/10) ** 2,
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : 1 - (-cos(19213 * pi / 10)) ** 2 = 1 - cos(19213*pi/10)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/5) = -cos(19213*pi/10),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (960),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) ** 2 = 1 - sin(pi/5) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_459 : -3*cos(pi/8)**2 + 3*sin(pi/8)**2 + 4*(-sin(pi/8)**2 + cos(pi/8)**2)**3=- sqrt( 2 ) / 2:=
begin
have : (-3) * (-sin(pi / 8) ** 2 + cos(pi / 8) ** 2) + 4 * (-sin(pi / 8) ** 2 + cos(pi / 8) ** 2) ** 3 = -3*cos(pi/8)**2 + 3*sin(pi/8)**2 + 4*(-sin(pi/8)**2 + cos(pi/8)**2)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(pi/8) ** 2 + cos(pi/8) ** 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(pi / 4) ** 3 - 3 * cos(pi / 4) = -3*cos(pi/4) + 4*cos(pi/4)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = 4 * cos(pi/4) ** 3 - 3 * cos(pi/4),
{
have : cos(3*pi/4) = cos(3*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_460 : cos(2*pi/7)=1 - 2*(-4*sin(1910*pi/21)**3 + 3*sin(1910*pi/21))**2:=
begin
have : 1 - 2 * ((-4) * sin(1910 * pi / 21) ** 3 + 3 * sin(1910 * pi / 21)) ** 2 = 1 - 2*(-4*sin(1910*pi/21)**3 + 3*sin(1910*pi/21))**2,
{
field_simp at *,
},
have : sin(pi/21) = sin(1910*pi/21),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/21) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - 2 * ((-4) * sin(pi / 21) ** 3 + 3 * sin(pi / 21)) ** 2 = 1 - 2*(-4*sin(pi/21)**3 + 3*sin(pi/21))**2,
{
field_simp at *,
},
have : sin(pi/7) = -4 * sin(pi/21) ** 3 + 3 * sin(pi/21),
{
have : sin(pi/7) = sin(3*(pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/7) = 1 - 2 * sin(pi/7) ** 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_461 : -cos(7677*pi/8)=sin(-pi/8)*cos(-2*pi) - 2*sin(-pi)*cos(-pi)*cos(-pi/8):=
begin
have : sin(-pi / 8) * cos((-2) * pi) - 2 * sin(-pi) * cos(-pi) * cos(-pi / 8) = sin(-pi/8)*cos(-2*pi) - 2*sin(-pi)*cos(-pi)*cos(-pi/8),
{
field_simp at *,
},
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
conv {to_rhs, rw ← this,},
have : sin(15*pi/8) = -cos(7677*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (15*pi/8) (480),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(15*pi/8) = sin(-pi/8) * cos(-2*pi) - sin(-2*pi) * cos(-pi/8),
{
have : sin(15*pi/8) = sin((-pi/8) - (-2*pi)),
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


lemma Trigo_number_generalization_step2_462 : -cos(1060*pi)=cos(pi):=
begin
have : 2 * (cos(pi) / 2 + 1 / 2) - 1 = cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : cos(pi) = -cos(1060*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (530),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 2 * cos(pi/2) ** 2 - 1,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_463 : cos(32563*pi/40)=sin(-pi/5)*sin(-pi/8) + cos(-13*pi/40)/2 + cos(-3*pi/40)/2:=
begin
have : cos(-3*pi/40) = cos(32563*pi/40),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-3*pi/40) (407),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 5) * sin(-pi / 8) + (cos((-3) * pi / 40) / 2 + cos((-13) * pi / 40) / 2) = sin(-pi/5)*sin(-pi/8) + cos(-13*pi/40)/2 + cos(-3*pi/40)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) * cos(-pi/8) = cos(-3*pi/40) / 2 + cos(-13*pi/40) / 2,
{
rw cos_mul_cos,
have : cos((-pi/5) + (-pi/8)) = cos(-13*pi/40),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (-pi/8)) = cos(-3*pi/40),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (cos(-pi/5) * cos(-pi/8)) = cos(-pi/5)*cos(-pi/8),
{
ring,
},
have : cos(-3*pi/40) = sin(-pi/5) * sin(-pi/8) + cos(-pi/5) * cos(-pi/8),
{
have : cos(-3*pi/40) = cos((-pi/5) - (-pi/8)),
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


lemma Trigo_number_generalization_step2_464 (h0 : cos(-pi/3)≠ 0) (h1 : (2*cos(-pi/3))≠ 0) (h2 : (2*cos(-pi/3)**3)≠ 0) : cos(763*pi/2)=3*sin(-2*pi/3)/(2*cos(-pi/3)) - sin(-2*pi/3)**3/(2*cos(-pi/3)**3):=
begin
have : (-4) * (sin((-2) * pi / 3) / (2 * cos(-pi / 3))) ** 3 + 3 * (sin((-2) * pi / 3) / (2 * cos(-pi / 3))) = 3*sin(-2*pi/3)/(2*cos(-pi/3)) - sin(-2*pi/3)**3/(2*cos(-pi/3)**3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = sin(-2*pi/3) / ( 2 * cos(-pi/3) ),
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
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(763*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (190),
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


lemma Trigo_number_generalization_step2_465 : sin(23309*pi/14)=-3*sin(17145*pi/14) + 4*sin(17145*pi/14)**3:=
begin
have : 4 * sin(17145 * pi / 14) ** 3 - 3 * sin(17145 * pi / 14) = -3*sin(17145*pi/14) + 4*sin(17145*pi/14)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = sin(17145*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/7) (612),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/7) = sin(23309*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/7) (832),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/7) = 4 * cos(pi/7) ** 3 - 3 * cos(pi/7),
{
have : cos(3*pi/7) = cos(3*(pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_466 : cos(-1199*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos((-1199) * pi / 4) = cos(-1199*pi/4),
{
field_simp at *,
},
have : sin(7025*pi/4) = cos(-1199*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7025*pi/4) (728),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(7025*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (878),
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


lemma Trigo_number_generalization_step2_467 (h0 : cos(pi/6)≠ 0) (h1 : (1-tan(pi/6)**2)≠ 0) (h2 : (1-(1/tan(232*pi/3))**2)≠ 0) (h3 : ((1-1/tan(232*pi/3)**2)*tan(232*pi/3))≠ 0) (h4 : tan(232*pi/3)≠ 0) : 2/((1 - 1/tan(232*pi/3)**2)*tan(232*pi/3))=sqrt( 3 ):=
begin
have : 2 * (1 / tan(232 * pi / 3)) / (1 - (1 / tan(232 * pi / 3)) ** 2) = 2/((1 - 1/tan(232*pi/3)**2)*tan(232*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(232*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 2 * tan(pi/6) / ( 1 - tan(pi/6) ** 2 ),
{
have : tan(pi/3) = tan(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_468 (h0 : cos(4183*pi/6)≠ 0) (h1 : (2*cos(4183*pi/6))≠ 0) : -sin(4183*pi/3)/(2*cos(4183*pi/6))=1 / 2:=
begin
have : -(sin(4183 * pi / 3) / (2 * cos(4183 * pi / 6))) = -sin(4183*pi/3)/(2*cos(4183*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(4183*pi/6) = sin(4183*pi/3) / ( 2 * cos(4183*pi/6) ),
{
have : sin(4183*pi/3) = sin(2*(4183*pi/6)),
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
have : sin(5*pi/6) = -sin(4183*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/6) (349),
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


lemma Trigo_number_generalization_step2_469 : sin(39631*pi/30)=-sin(pi/5)*sin(pi/3) + (-1 + 2*cos(pi/10)**2)*cos(pi/3):=
begin
have : -sin(pi / 5) * sin(pi / 3) + (2 * cos(pi / 10) ** 2 - 1) * cos(pi / 3) = -sin(pi/5)*sin(pi/3) + (-1 + 2*cos(pi/10)**2)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = 2 * cos(pi/10) ** 2 - 1,
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(8*pi/15) = sin(39631*pi/30),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (8*pi/15) (660),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi/15) = - sin(pi/5) * sin(pi/3) + cos(pi/5) * cos(pi/3),
{
have : cos(8*pi/15) = cos((pi/5) + (pi/3)),
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


lemma Trigo_number_generalization_step2_470 : -sin(pi/3)**2 + (1 - 2*sin(pi/6)**2)**2=- 1 / 2:=
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
have : cos(2*pi/3) = -sin(pi/3) ** 2 + cos(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_471 : (cos(-pi/6)*cos(38189*pi/24) + sin(-pi/6)*sin(38189*pi/24))**2=1 - cos(-pi/8) ** 2:=
begin
have : (sin(38189 * pi / 24) * sin(-pi / 6) + cos(38189 * pi / 24) * cos(-pi / 6)) ** 2 = (cos(-pi/6)*cos(38189*pi/24) + sin(-pi/6)*sin(38189*pi/24))**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(12731*pi/8) = sin(38189*pi/24) * sin(-pi/6) + cos(38189*pi/24) * cos(-pi/6),
{
have : cos(12731*pi/8) = cos((38189*pi/24) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = cos(12731*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (795),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) ** 2 = 1 - cos(-pi/8) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_472 (h0 : sin(-pi/4)≠ 0) (h1 : (2*sin(-pi/4))≠ 0) (h2 : (2*cos(4611*pi/4))≠ 0) : sin(-pi/2)/(2*cos(4611*pi/4))=- cos(7677*pi/4):=
begin
have : sin(-pi/4) = cos(4611*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (576),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(-pi/2) / ( 2 * sin(-pi/4) ),
{
have : sin(-pi/2) = sin(2*(-pi/4)),
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
have : cos(-pi/4) = - cos(7677*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (959),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_473 : -sin(-2503*pi/4)=- sqrt( 2 ) / 2:=
begin
have : -sin((-2503) * pi / 4) = -sin(-2503*pi/4),
{
field_simp at *,
},
have : cos(6049*pi/4) = sin(-2503*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (6049*pi/4) (443),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -cos(6049*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (756),
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


lemma Trigo_number_generalization_step2_474 : (-4*sin(pi/21)**3 + 3*sin(pi/21))*sin(4995*pi/8)=- sin(-15*pi/56) / 2 + sin(pi/56) / 2:=
begin
have : ((-4) * sin(pi / 21) ** 3 + 3 * sin(pi / 21)) * sin(4995 * pi / 8) = (-4*sin(pi/21)**3 + 3*sin(pi/21))*sin(4995*pi/8),
{
field_simp at *,
},
have : sin(pi/7) = -4 * sin(pi/21) ** 3 + 3 * sin(pi/21),
{
have : sin(pi/7) = sin(3*(pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = sin(4995*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/8) (312),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) * cos(-pi/8) = - sin(-15*pi/56) / 2 + sin(pi/56) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/8) + (pi/7)) = sin(pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/8) - (pi/7)) = sin(-15*pi/56),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_475 (h0 : sin(2*pi/21)≠ 0) (h1 : (2*sin(2*pi/21))≠ 0) (h2 : sin(2*pi/21)≠ 0) : -sin(pi/8)*cos(11*pi/24) - sin(-pi/7) + sin(11*pi/24)*cos(pi/8)=sin(4*pi/21)*sin(5*pi/21)/sin(2*pi/21):=
begin
have : sin(11 * pi / 24) * cos(pi / 8) - sin(pi / 8) * cos(11 * pi / 24) - sin(-pi / 7) = -sin(pi/8)*cos(11*pi/24) - sin(-pi/7) + sin(11*pi/24)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(11*pi/24) * cos(pi/8) - sin(pi/8) * cos(11*pi/24),
{
have : sin(pi/3) = sin((11*pi/24) - (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(5 * pi / 21) * (sin(4 * pi / 21) / (2 * sin(2 * pi / 21))) = sin(4*pi/21)*sin(5*pi/21)/sin(2*pi/21),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/21) = sin(4*pi/21) / ( 2 * sin(2*pi/21) ),
{
have : sin(4*pi/21) = sin(2*(2*pi/21)),
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
have : sin(pi/3) - sin(-pi/7) = 2 * sin(5*pi/21) * cos(2*pi/21),
{
rw sin_sub_sin,
have : cos(((pi/3) + (-pi/7))/2) = cos(2*pi/21),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (-pi/7))/2) = sin(5*pi/21),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_476 : sin(2811*pi/2) - 2*sin(pi/10)**2 + 1=2 * cos(3*pi/5) * cos(-2*pi/5):=
begin
have : sin(2811 * pi / 2) + (1 - 2 * sin(pi / 10) ** 2) = sin(2811*pi/2) - 2*sin(pi/10)**2 + 1,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = 1 - 2 * sin(pi/10) ** 2,
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi / 5) + sin(2811 * pi / 2) = sin(2811*pi/2) + cos(pi/5),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(2811*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (703),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) + cos(-pi) = 2 * cos(3*pi/5) * cos(-2*pi/5),
{
rw cos_add_cos,
have : cos(((pi/5) + (-pi))/2) = cos(-2*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/5) - (-pi))/2) = cos(3*pi/5),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_477 (h0 : sin(pi/8)≠ 0) (h1 : (2*sin(pi/8))≠ 0) (h2 : (4*sin(pi/8)**2)≠ 0) : sin(pi/4)**2/(4*sin(pi/8)**2)=1/2 - cos(1997*pi/4)/2:=
begin
have : -cos(1997 * pi / 4) / 2 + 1 / 2 = 1/2 - cos(1997*pi/4)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = -cos(1997*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (249),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (sin(pi / 4) / (2 * sin(pi / 8))) ** 2 = sin(pi/4)**2/(4*sin(pi/8)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = sin(pi/4) / ( 2 * sin(pi/8) ),
{
have : sin(pi/4) = sin(2*(pi/8)),
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
have : cos(pi/8) ** 2 = cos(pi/4) / 2 + 1 / 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
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


lemma Trigo_number_generalization_step2_478 (h0 : cos(2200*pi/3)≠ 0) (h1 : (2*cos(2200*pi/3))≠ 0) : -sin(4400*pi/3)/(2*cos(2200*pi/3))=sqrt( 3 ) / 2:=
begin
have : -(sin(4400 * pi / 3) / (2 * cos(2200 * pi / 3))) = -sin(4400*pi/3)/(2*cos(2200*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2200*pi/3) = sin(4400*pi/3) / ( 2 * cos(2200*pi/3) ),
{
have : sin(4400*pi/3) = sin(2*(2200*pi/3)),
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
have : sin(2*pi/3) = -sin(2200*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/3) (367),
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


lemma Trigo_number_generalization_step2_479 (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))/(2*cos(pi))=0:=
begin
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) / (2 * cos(pi)) = (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))/(2*cos(pi)),
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_480 : -cos(459*pi/8)=4 * cos(-pi/8) ** 3 - 3 * cos(-pi/8):=
begin
have : cos(6373*pi/8) = cos(459*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (6373*pi/8) (427),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/8) = -cos(6373*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-3*pi/8) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/8) = 4 * cos(-pi/8) ** 3 - 3 * cos(-pi/8),
{
have : cos(-3*pi/8) = cos(3*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_481 : sin(-pi/6)=-1 + 2*sin(2029*pi/6)**2:=
begin
have : 1 - 2 * (1 - sin(2029 * pi / 6) ** 2) = -1 + 2*sin(2029*pi/6)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2029*pi/6) ** 2 = 1 - sin(2029*pi/6) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : -(2 * cos(2029 * pi / 6) ** 2 - 1) = 1 - 2*cos(2029*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2029*pi/3) = 2 * cos(2029*pi/6) ** 2 - 1,
{
have : cos(2029*pi/3) = cos(2*(2029*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = - cos(2029*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (338),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_482 : 3*sin(-4*pi/45)*cos(-pi/5) - 4*(sin(-4*pi/45)*cos(-pi/5) - sin(-pi/5)*cos(-4*pi/45))**3 - 3*sin(-pi/5)*cos(-4*pi/45)=sqrt( 3 ) / 2:=
begin
have : (-4) * (sin((-4) * pi / 45) * cos(-pi / 5) - sin(-pi / 5) * cos((-4) * pi / 45)) ** 3 + 3 * (sin((-4) * pi / 45) * cos(-pi / 5) - sin(-pi / 5) * cos((-4) * pi / 45)) = 3*sin(-4*pi/45)*cos(-pi/5) - 4*(sin(-4*pi/45)*cos(-pi/5) - sin(-pi/5)*cos(-4*pi/45))**3 - 3*sin(-pi/5)*cos(-4*pi/45),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(-4*pi/45) * cos(-pi/5) - sin(-pi/5) * cos(-4*pi/45),
{
have : sin(pi/9) = sin((-4*pi/45) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 9) ** 3 + 3 * sin(pi / 9) = -4*sin(pi/9)**3 + 3*sin(pi/9),
{
field_simp at *,
},
have : sin(pi/3) = -4 * sin(pi/9) ** 3 + 3 * sin(pi/9),
{
have : sin(pi/3) = sin(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_483 : -sin(3169*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(1995*pi/4) = -sin(3169*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (1995*pi/4) (146),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = cos(1995*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/4) (249),
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


lemma Trigo_number_generalization_step2_484 (h0 : cos(pi/8)≠ 0) (h1 : (1-tan(pi/8)**2)≠ 0) (h2 : (1-tan(1801*pi/8)**2)≠ 0) : 2*tan(1801*pi/8)/(1 - tan(1801*pi/8)**2)=1:=
begin
have : tan(pi/8) = tan(1801*pi/8),
{
rw tan_eq_tan_add_int_mul_pi (pi/8) (225),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 2 * tan(pi/8) / ( 1 - tan(pi/8) ** 2 ),
{
have : tan(pi/4) = tan(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_485 : -sin(4513*pi/8)**2 + cos(-pi/8)**2=2 * cos(-pi/8) ** 2 - 1:=
begin
have : -(-sin(4513 * pi / 8)) ** 2 + cos(-pi / 8) ** 2 = -sin(4513*pi/8)**2 + cos(-pi/8)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -sin(4513*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/8) (282),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -sin(-pi/8) ** 2 + cos(-pi/8) ** 2,
{
have : cos(-pi/4) = cos(2*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = 2 * cos(-pi/8) ** 2 - 1,
{
have : cos(-pi/4) = cos(2*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_486 : cos(564*pi)**2=1/2 + cos(4*pi)/2:=
begin
have : cos(2*pi) = cos(564*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (281),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (1 / 2 - cos(4 * pi) / 2) = 1/2 + cos(4*pi)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) ** 2 = 1 / 2 - cos(4*pi) / 2,
{
have : cos(4*pi) = cos(2*(2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) ** 2 = 1 - sin(2*pi) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_487 : -1 + 2*cos(-pi/144)**2=sin(pi/9)*sin(pi/8) + cos(17*pi/72)/2 + cos(-pi/72)/2:=
begin
have : 2 * cos(-pi / 144) ** 2 - 1 = -1 + 2*cos(-pi/144)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/72) = 2 * cos(-pi/144) ** 2 - 1,
{
have : cos(-pi/72) = cos(2*(-pi/144)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 9) * sin(pi / 8) + (cos(-pi / 72) / 2 + cos(17 * pi / 72) / 2) = sin(pi/9)*sin(pi/8) + cos(17*pi/72)/2 + cos(-pi/72)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) * cos(pi/8) = cos(-pi/72) / 2 + cos(17*pi/72) / 2,
{
rw cos_mul_cos,
have : cos((pi/9) + (pi/8)) = cos(17*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (pi/8)) = cos(-pi/72),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (cos(pi/9) * cos(pi/8)) = cos(pi/9)*cos(pi/8),
{
ring,
},
have : cos(-pi/72) = sin(pi/9) * sin(pi/8) + cos(pi/9) * cos(pi/8),
{
have : cos(-pi/72) = cos((pi/9) - (pi/8)),
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


lemma Trigo_number_generalization_step2_488 : cos(2*pi/7)=1 - 2*sin(9995*pi/7)**2:=
begin
have : 1 - 2 * (-sin(9995 * pi / 7)) ** 2 = 1 - 2*sin(9995*pi/7)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(5676*pi/7) = -sin(9995*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5676*pi/7) (308),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = sin(5676*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/7) (405),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/7) = 1 - 2 * sin(pi/7) ** 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_489 : -1 - cos(-pi) + 2*cos(pi/16)**2=2*sin(-7*pi/16)*sin(26169*pi/16):=
begin
have : (-2) * -sin(26169 * pi / 16) * sin((-7) * pi / 16) = 2*sin(-7*pi/16)*sin(26169*pi/16),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(9*pi/16) = -sin(26169*pi/16),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (9*pi/16) (817),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * cos(pi / 16) ** 2 - 1 - cos(-pi) = -1 - cos(-pi) + 2*cos(pi/16)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = 2 * cos(pi/16) ** 2 - 1,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) - cos(-pi) = - 2 * sin(9*pi/16) * sin(-7*pi/16),
{
rw cos_sub_cos,
have : sin(((pi/8) + (-pi))/2) = sin(-7*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/8) - (-pi))/2) = sin(9*pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_490 : -cos(959*pi)**2 + sin(959*pi)**2=- 1:=
begin
have : -(-sin(959 * pi) ** 2 + cos(959 * pi) ** 2) = -cos(959*pi)**2 + sin(959*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1918*pi) = -sin(959*pi) ** 2 + cos(959*pi) ** 2,
{
have : cos(1918*pi) = cos(2*(959*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(1918*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (958),
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


lemma Trigo_number_generalization_step2_491 : 2*(1 - 2*sin(pi/18)**2)*sin(-pi/16)*cos(-pi/16)=- sin(17*pi/72) / 2 + sin(-pi/72) / 2:=
begin
have : (1 - 2 * sin(pi / 18) ** 2) * (2 * sin(-pi / 16) * cos(-pi / 16)) = 2*(1 - 2*sin(pi/18)**2)*sin(-pi/16)*cos(-pi/16),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = 2 * sin(-pi/16) * cos(-pi/16),
{
have : sin(-pi/8) = sin(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 8) * (1 - 2 * sin(pi / 18) ** 2) = (1 - 2*sin(pi/18)**2)*sin(-pi/8),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = 1 - 2 * sin(pi/18) ** 2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) * cos(pi/9) = - sin(17*pi/72) / 2 + sin(-pi/72) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/9) + (-pi/8)) = sin(-pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/9) - (-pi/8)) = sin(17*pi/72),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_492 : sin(14713*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(14371*pi/12) = sin(14713*pi/12),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (14371*pi/12) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(14371*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (598),
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


lemma Trigo_number_generalization_step2_493 : cos(631*pi/4)/2 + cos(633*pi/4)/2=cos(-9*pi/4) / 2 + cos(-7*pi/4) / 2:=
begin
have : cos(158*pi) * cos(pi/4) = cos(631*pi/4) / 2 + cos(633*pi/4) / 2,
{
rw cos_mul_cos,
have : cos((158*pi) + (pi/4)) = cos(633*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((158*pi) - (pi/4)) = cos(631*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(158*pi) * cos(pi/4)) = cos(pi/4)*cos(158*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(158 * pi) * cos(pi / 4) = cos(pi/4)*cos(158*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(158*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) * cos(pi/4) = cos(-9*pi/4) / 2 + cos(-7*pi/4) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (pi/4)) = cos(-7*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/4)) = cos(-9*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_494 : -cos(-pi/9)*cos(27079*pi/18) - sin(-pi/9)*sin(27079*pi/18)=- sin(1801*pi):=
begin
have : -(sin(27079 * pi / 18) * sin(-pi / 9) + cos(27079 * pi / 18) * cos(-pi / 9)) = -cos(-pi/9)*cos(27079*pi/18) - sin(-pi/9)*sin(27079*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3009*pi/2) = sin(27079*pi/18) * sin(-pi/9) + cos(27079*pi/18) * cos(-pi/9),
{
have : cos(3009*pi/2) = cos((27079*pi/18) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(3009*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (752),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(1801*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (901),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_495 (h0 : cos(pi)≠ 0) (h1 : (1-tan(pi)**2)≠ 0) (h2 : (1-(sin(pi)/cos(pi))**2)≠ 0) (h3 : cos(pi)≠ 0) (h4 : ((-sin(pi)**2/cos(pi)**2+1)*cos(pi))≠ 0) : 2*sin(pi)/((-sin(pi)**2/cos(pi)**2 + 1)*cos(pi))=- 1 / tan(1239*pi/2):=
begin
have : 2 * (sin(pi) / cos(pi)) / (1 - (sin(pi) / cos(pi)) ** 2) = 2*sin(pi)/((-sin(pi)**2/cos(pi)**2 + 1)*cos(pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = 2 * tan(pi) / ( 1 - tan(pi) ** 2 ),
{
have : tan(2*pi) = tan(2*(pi)),
{
apply congr_arg,
ring,
},
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - 1 / tan(1239*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi) (617),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_496 : -2*sin(16123*pi/28)*cos(16123*pi/28)=cos(3319*pi/7):=
begin
have : -(2 * sin(16123 * pi / 28) * cos(16123 * pi / 28)) = -2*sin(16123*pi/28)*cos(16123*pi/28),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(16123*pi/14) = 2 * sin(16123*pi/28) * cos(16123*pi/28),
{
have : sin(16123*pi/14) = sin(2*(16123*pi/28)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = -sin(16123*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (575),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = cos(3319*pi/7),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/7) (237),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_497 : 1 - 2*sin(451*pi/10)**2=- cos(846*pi/5):=
begin
have : sin(-pi/10) = sin(451*pi/10),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/10) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = 1 - 2 * sin(-pi/10) ** 2,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = - cos(846*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/5) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_498 (h0 : cos((2600*pi/3)/2)≠ 0) (h1 : sin(2600*pi/3)≠ 0) : -(1 - cos(2600*pi/3))/sin(2600*pi/3)=- sqrt( 3 ):=
begin
have : -((1 - cos(2600 * pi / 3)) / sin(2600 * pi / 3)) = -(1 - cos(2600*pi/3))/sin(2600*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1300*pi/3) = ( 1 - cos(2600*pi/3) ) / sin(2600*pi/3),
{
have : tan(1300*pi/3) = tan((2600*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(1300*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (434),
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


lemma Trigo_number_generalization_step2_499 (h0 : cos(-2*pi)≠ 0) (h1 : (2*cos((-2)*pi))≠ 0) (h2 : (2*cos(-2*pi))≠ 0) : (sin(-pi/5)*cos(-19*pi/5) + sin(-19*pi/5)*cos(-pi/5))/(2*cos(-2*pi))=2 * sin(-pi) * cos(-pi):=
begin
have : (sin((-19) * pi / 5) * cos(-pi / 5) + sin(-pi / 5) * cos((-19) * pi / 5)) / (2 * cos((-2) * pi)) = (sin(-pi/5)*cos(-19*pi/5) + sin(-19*pi/5)*cos(-pi/5))/(2*cos(-2*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-4*pi) = sin(-19*pi/5) * cos(-pi/5) + sin(-pi/5) * cos(-19*pi/5),
{
have : sin(-4*pi) = sin((-19*pi/5) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_500 : sin(16763*pi/10)=sin(17603*pi/10):=
begin
have : sin(16723*pi/10) = sin(16763*pi/10),
{
rw sin_eq_sin_add_int_mul_two_pi (16723*pi/10) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = sin(16723*pi/10),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/5) (836),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = sin(17603*pi/10),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/5) (880),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_501 : sin(1444*pi)=-sin(1761*pi/4)**2 + cos(pi/4)**2:=
begin
have : cos(pi/2) = sin(1444*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (722),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(1761*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (220),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(pi/4) ** 2 + cos(pi/4) ** 2,
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
rw this,
end


lemma Trigo_number_generalization_step2_502 : sin(pi/8)*sin(5431*pi/8) + sin(5*pi/8)*cos(pi/8)=1:=
begin
have : -sin(pi / 8) * -sin(5431 * pi / 8) + sin(5 * pi / 8) * cos(pi / 8) = sin(pi/8)*sin(5431*pi/8) + sin(5*pi/8)*cos(pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/8) = -sin(5431*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/8) (339),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 8) * cos(pi / 8) - sin(pi / 8) * cos(5 * pi / 8) = -sin(pi/8)*cos(5*pi/8) + sin(5*pi/8)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(5*pi/8) * cos(pi/8) - sin(pi/8) * cos(5*pi/8),
{
have : sin(pi/2) = sin((5*pi/8) - (pi/8)),
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


lemma Trigo_number_generalization_step2_503 : sin(4033*pi/6)=-sin(-3133*pi/6):=
begin
have : -sin((-3133) * pi / 6) = -sin(-3133*pi/6),
{
field_simp at *,
},
have : cos(3362*pi/3) = sin(-3133*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3362*pi/3) (299),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(4033*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (336),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - cos(3362*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (560),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_504 (h0 : tan(1061*pi/12)≠ 0) (h1 : (sin(1061*pi/12)/cos(1061*pi/12))≠ 0) (h2 : sin(1061*pi/12)≠ 0) (h3 : cos(1061*pi/12)≠ 0) : cos(1061*pi/12)/sin(1061*pi/12)=2 - sqrt( 3 ):=
begin
have : 1 / (sin(1061 * pi / 12) / cos(1061 * pi / 12)) = cos(1061*pi/12)/sin(1061*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1061*pi/12) = sin(1061*pi/12) / cos(1061*pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 1 / tan(1061*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (88),
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


lemma Trigo_number_generalization_step2_505 : 1 - 2*cos(18415*pi/24)**2=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(2 * cos(18415 * pi / 24) ** 2 - 1) = 1 - 2*cos(18415*pi/24)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(18415*pi/12) = 2 * cos(18415*pi/24) ** 2 - 1,
{
have : cos(18415*pi/12) = cos(2*(18415*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(18415*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/12) (767),
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


lemma Trigo_number_generalization_step2_506 : cos(476*pi)=1:=
begin
have : cos(116*pi) = cos(476*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (116*pi) (180),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(116*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (57),
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


lemma Trigo_number_generalization_step2_507 : -sin(-pi/9)*sin(13*pi/36) + (1 - 2*sin(13*pi/72)**2)*cos(-pi/9)=sqrt( 2 ) / 2:=
begin
have : -sin(-pi / 9) * sin(13 * pi / 36) + cos(-pi / 9) * (1 - 2 * sin(13 * pi / 72) ** 2) = -sin(-pi/9)*sin(13*pi/36) + (1 - 2*sin(13*pi/72)**2)*cos(-pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/36) = 1 - 2 * sin(13*pi/72) ** 2,
{
have : cos(13*pi/36) = cos(2*(13*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : -sin(13 * pi / 36) * sin(-pi / 9) + cos(13 * pi / 36) * cos(-pi / 9) = -sin(-pi/9)*sin(13*pi/36) + cos(-pi/9)*cos(13*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(13*pi/36) * sin(-pi/9) + cos(13*pi/36) * cos(-pi/9),
{
have : cos(pi/4) = cos((13*pi/36) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_508 (h0 : tan(5551*pi/6)≠ 0) : -1/tan(5551*pi/6)=- sqrt( 3 ):=
begin
have : (-1) / tan(5551 * pi / 6) = -1/tan(5551*pi/6),
{
field_simp at *,
},
have : tan(188*pi/3) = -1 / tan(5551*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (188*pi/3) (862),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = tan(188*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (2*pi/3) (62),
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


lemma Trigo_number_generalization_step2_509 : -sin(14192*pi/9)=1 - 2*sin(34657*pi/36)**2:=
begin
have : sin(-pi/9) = -sin(14192*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (788),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(34657*pi/18) = 1 - 2 * sin(34657*pi/36) ** 2,
{
have : cos(34657*pi/18) = cos(2*(34657*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = cos(34657*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (962),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_510 : -sin(12675*pi/8)=- 4 * sin(-pi/8) ** 3 + 3 * sin(-pi/8):=
begin
have : sin(12459*pi/8) = -sin(12675*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (12459*pi/8) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/8) = sin(12459*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-3*pi/8) (778),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/8) = - 4 * sin(-pi/8) ** 3 + 3 * sin(-pi/8),
{
have : sin(-3*pi/8) = sin(3*(-pi/8)),
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


lemma Trigo_number_generalization_step2_511 : -1 + 2*sin(1480*pi)**2=- cos(200*pi):=
begin
have : -1 + 2 * (-sin(1480 * pi)) ** 2 = -1 + 2*sin(1480*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(1480*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (739),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 2) ** 2 - 1 = -1 + 2*cos(pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 2 * cos(pi/2) ** 2 - 1,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(200*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_512 : 1 - 2*sin(7721*pi/8)**2=sqrt( 2 ) / 2:=
begin
have : cos(7721*pi/4) = 1 - 2 * sin(7721*pi/8) ** 2,
{
have : cos(7721*pi/4) = cos(2*(7721*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(7721*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (965),
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


lemma Trigo_number_generalization_step2_513 : -1 + cos(-pi/6) + 2*cos(8981*pi/10)**2=2 * cos(-pi/60) * cos(-11*pi/60):=
begin
have : cos(-pi/10) = cos(8981*pi/10),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/10) (449),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(-pi / 10) ** 2 - 1 + cos(-pi / 6) = -1 + cos(-pi/6) + 2*cos(-pi/10)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = 2 * cos(-pi/10) ** 2 - 1,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) + cos(-pi/6) = 2 * cos(-pi/60) * cos(-11*pi/60),
{
rw cos_add_cos,
have : cos(((-pi/5) + (-pi/6))/2) = cos(-11*pi/60),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/5) - (-pi/6))/2) = cos(-pi/60),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_514 : cos(15743*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos(15743 * pi / 6) = cos(15743*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5717*pi/6) = -cos(15743*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5717*pi/6) (835),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(5717*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (476),
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


lemma Trigo_number_generalization_step2_515 : -sin(5*pi/2)*cos(265*pi/2) + cos(2*pi)*cos(5*pi/2)=0:=
begin
have : -cos(265 * pi / 2) * sin(5 * pi / 2) + cos(2 * pi) * cos(5 * pi / 2) = -sin(5*pi/2)*cos(265*pi/2) + cos(2*pi)*cos(5*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(265*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 2) * sin(2 * pi) + cos(5 * pi / 2) * cos(2 * pi) = sin(2*pi)*sin(5*pi/2) + cos(2*pi)*cos(5*pi/2),
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
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_516 : -sin(5941*pi/6)**2 + cos(5941*pi/6)**2=1 / 2:=
begin
have : cos(5941*pi/3) = -sin(5941*pi/6) ** 2 + cos(5941*pi/6) ** 2,
{
have : cos(5941*pi/3) = cos(2*(5941*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(5941*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (990),
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


lemma Trigo_number_generalization_step2_517 (h0 : sin(3263*pi/10)≠ 0) (h1 : cos((2*pi/5)/2)≠ 0) (h2 : sin(2*pi/5)≠ 0) : sin(pi/5)/sin(3263*pi/10)=(1 - cos(2*pi/5))/sin(2*pi/5):=
begin
have : tan(pi/5) = ( 1 - cos(2*pi/5) ) / sin(2*pi/5),
{
have : tan(pi/5) = tan((2*pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = sin(3263*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (163),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) / cos(pi/5) = tan(pi/5),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_518 (h0 : cos(-pi/6)≠ 0) (h1 : cos(1319*pi/6)≠ 0) : sin(5627*pi/6)/cos(1319*pi/6)=tan(-pi/6):=
begin
have : cos(-pi/6) = cos(1319*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (110),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(5627*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (469),
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


lemma Trigo_number_generalization_step2_519 : -cos(5345*pi/2)=0:=
begin
have : sin(1501*pi) = cos(5345*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1501*pi) (585),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(1501*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (751),
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


lemma Trigo_number_generalization_step2_520 : sin(-pi/3)*cos(pi/2) - sin(pi/2)*cos(5776*pi/3)=1 / 2:=
begin
have : sin(-pi / 3) * cos(pi / 2) + sin(pi / 2) * -cos(5776 * pi / 3) = sin(-pi/3)*cos(pi/2) - sin(pi/2)*cos(5776*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(5776*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (962),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-pi/3) * cos(pi/2) + sin(pi/2) * cos(-pi/3),
{
have : sin(pi/6) = sin((-pi/3) + (pi/2)),
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


lemma Trigo_number_generalization_step2_521 : -sin(pi/6) + sin(17486*pi/9)=-2*sin(-pi/36)*sin(10633*pi/36):=
begin
have : sin(17486 * pi / 9) - sin(pi / 6) = -sin(pi/6) + sin(17486*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(17486*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (971),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 36) * -sin(10633 * pi / 36) = -2*sin(-pi/36)*sin(10633*pi/36),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/36) = -sin(10633*pi/36),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/36) (147),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/9) - sin(pi/6) = 2 * sin(-pi/36) * cos(5*pi/36),
{
rw sin_sub_sin,
have : cos(((pi/9) + (pi/6))/2) = cos(5*pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/9) - (pi/6))/2) = sin(-pi/36),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_522 : 2*(sin(-31*pi/168)*cos(pi/7) + sin(pi/7)*cos(-31*pi/168))*cos(-pi/24)=sin(pi/6) * cos(pi/4) - sin(pi/4) * cos(pi/6):=
begin
have : 2 * (sin((-31) * pi / 168) * cos(pi / 7) + sin(pi / 7) * cos((-31) * pi / 168)) * cos(-pi / 24) = 2*(sin(-31*pi/168)*cos(pi/7) + sin(pi/7)*cos(-31*pi/168))*cos(-pi/24),
{
field_simp at *,
},
have : sin(-pi/24) = sin(-31*pi/168) * cos(pi/7) + sin(pi/7) * cos(-31*pi/168),
{
have : sin(-pi/24) = sin((-31*pi/168) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = 2 * sin(-pi/24) * cos(-pi/24),
{
have : sin(-pi/12) = sin(2*(-pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = sin(pi/6) * cos(pi/4) - sin(pi/4) * cos(pi/6),
{
have : sin(-pi/12) = sin((pi/6) - (pi/4)),
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


lemma Trigo_number_generalization_step2_523 (h0 : tan(10273*pi/10)≠ 0) : -1/tan(10273*pi/10)=tan(294*pi/5):=
begin
have : (-1) / tan(10273 * pi / 10) = -1/tan(10273*pi/10),
{
field_simp at *,
},
have : tan(509*pi/5) = -1 / tan(10273*pi/10),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (509*pi/5) (925),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = tan(509*pi/5),
{
rw tan_eq_tan_add_int_mul_pi (-pi/5) (102),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = tan(294*pi/5),
{
rw tan_eq_tan_add_int_mul_pi (-pi/5) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_524 : cos(-pi/3)=2*sin(22063*pi/12)*cos(10387*pi/12):=
begin
have : (-2) * -sin(22063 * pi / 12) * cos(10387 * pi / 12) = 2*sin(22063*pi/12)*cos(10387*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(10387*pi/12) = -sin(22063*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (10387*pi/12) (486),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(2 * sin(10387 * pi / 12) * cos(10387 * pi / 12)) = -2*sin(10387*pi/12)*cos(10387*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(10387*pi/6) = 2 * sin(10387*pi/12) * cos(10387*pi/12),
{
have : sin(10387*pi/6) = sin(2*(10387*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(10387*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (865),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_525 : 1 - 2*cos(1572*pi/5)**2=- cos(456*pi/5):=
begin
have : 1 - 2 * (-cos(1572 * pi / 5)) ** 2 = 1 - 2*cos(1572*pi/5)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/10) = -cos(1572*pi/5),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/10) (157),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = 1 - 2 * sin(-pi/10) ** 2,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = - cos(456*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/5) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_526 : cos(pi/8)=((sin(-19*pi/24)*cos(-pi/3) + sin(-pi/3)*cos(-19*pi/24))*cos(pi) + sin(pi)*cos(-9*pi/8))*sin(-pi/4) + cos(-pi/4)*cos(-pi/8):=
begin
have : ((sin((-19) * pi / 24) * cos(-pi / 3) + sin(-pi / 3) * cos((-19) * pi / 24)) * cos(pi) + sin(pi) * cos((-9) * pi / 8)) * sin(-pi / 4) + cos(-pi / 4) * cos(-pi / 8) = ((sin(-19*pi/24)*cos(-pi/3) + sin(-pi/3)*cos(-19*pi/24))*cos(pi) + sin(pi)*cos(-9*pi/8))*sin(-pi/4) + cos(-pi/4)*cos(-pi/8),
{
field_simp at *,
},
have : sin(-9*pi/8) = sin(-19*pi/24) * cos(-pi/3) + sin(-pi/3) * cos(-19*pi/24),
{
have : sin(-9*pi/8) = sin((-19*pi/24) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : (sin((-9) * pi / 8) * cos(pi) + sin(pi) * cos((-9) * pi / 8)) * sin(-pi / 4) + cos(-pi / 8) * cos(-pi / 4) = (sin(-9*pi/8)*cos(pi) + sin(pi)*cos(-9*pi/8))*sin(-pi/4) + cos(-pi/4)*cos(-pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) = sin(-9*pi/8) * cos(pi) + sin(pi) * cos(-9*pi/8),
{
have : sin(-pi/8) = sin((-9*pi/8) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = sin(-pi/8) * sin(-pi/4) + cos(-pi/8) * cos(-pi/4),
{
have : cos(pi/8) = cos((-pi/8) - (-pi/4)),
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


lemma Trigo_number_generalization_step2_527 (h0 : sin(pi/5)≠ 0) (h1 : (2*sin(pi/5))≠ 0) : sin(2*pi/5)/(2*sin(pi/5))=-cos(-7896*pi/5):=
begin
have : -cos((-7896) * pi / 5) = -cos(-7896*pi/5),
{
field_simp at *,
},
have : cos(8906*pi/5) = cos(-7896*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (8906*pi/5) (101),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = sin(2*pi/5) / ( 2 * sin(pi/5) ),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
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
have : cos(pi/5) = - cos(8906*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/5) (890),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_528 (h0 : cos(3883*pi/2)≠ 0) (h1 : (2*cos(3883*pi/2))≠ 0) : sin(3883*pi)/(2*cos(3883*pi/2))=2 * cos(pi/2) ** 2 - 1:=
begin
have : sin(3883*pi/2) = sin(3883*pi) / ( 2 * cos(3883*pi/2) ),
{
have : sin(3883*pi) = sin(2*(3883*pi/2)),
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
have : cos(pi) = sin(3883*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (971),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 2 * cos(pi/2) ** 2 - 1,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_529 : -1 + 2*cos(10669*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : 2 * cos(10669 * pi / 12) ** 2 - 1 = -1 + 2*cos(10669*pi/12)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(10669*pi/6) = 2 * cos(10669*pi/12) ** 2 - 1,
{
have : cos(10669*pi/6) = cos(2*(10669*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(10669*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (889),
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


lemma Trigo_number_generalization_step2_530 : -sin(3073*pi/4)=- 4 * sin(-pi/4) ** 3 + 3 * sin(-pi/4):=
begin
have : sin(4851*pi/4) = sin(3073*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4851*pi/4) (990),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/4) = -sin(4851*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-3*pi/4) (606),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/4) = - 4 * sin(-pi/4) ** 3 + 3 * sin(-pi/4),
{
have : sin(-3*pi/4) = sin(3*(-pi/4)),
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


lemma Trigo_number_generalization_step2_531 (h0 : cos(-pi/12)≠ 0) (h1 : (1-tan(-pi/12)**2)≠ 0) (h2 : cos(-pi/24)≠ 0) (h3 : (1-(2*tan(-pi/24)/(1-tan(-pi/24)**2))**2)≠ 0) (h4 : (1-tan(-pi/24)**2)≠ 0) (h5 : ((1-tan(-pi/24)**2)*(-4*tan(-pi/24)**2/(1-tan(-pi/24)**2)**2+1))≠ 0) : sin(-pi/6) / cos(-pi/6)=4*tan(-pi/24)/((1 - tan(-pi/24)**2)*(-4*tan(-pi/24)**2/(1 - tan(-pi/24)**2)**2 + 1)):=
begin
have : 2 * (2 * tan(-pi / 24) / (1 - tan(-pi / 24) ** 2)) / (1 - (2 * tan(-pi / 24) / (1 - tan(-pi / 24) ** 2)) ** 2) = 4*tan(-pi/24)/((1 - tan(-pi/24)**2)*(-4*tan(-pi/24)**2/(1 - tan(-pi/24)**2)**2 + 1)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/12) = 2 * tan(-pi/24) / ( 1 - tan(-pi/24) ** 2 ),
{
have : tan(-pi/12) = tan(2*(-pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-pi/6) / cos(-pi/6) = tan(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_532 : 4*(cos(-pi/2)/2 + 1/2)*sin(-pi/4)**2=1 / 2 - cos(-pi) / 2:=
begin
have : 4 * sin(-pi / 4) ** 2 * (cos(-pi / 2) / 2 + 1 / 2) = 4*(cos(-pi/2)/2 + 1/2)*sin(-pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) ** 2 = cos(-pi/2) / 2 + 1 / 2,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * sin(-pi / 4) * cos(-pi / 4)) ** 2 = 4*sin(-pi/4)**2*cos(-pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(-pi/2) ** 2 = 1 / 2 - cos(-pi) / 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
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


lemma Trigo_number_generalization_step2_533 : cos(-pi/7)*cos(6291*pi/14) - sin(-pi/7)*sin(9*pi/14)=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : cos(9*pi/14) = cos(6291*pi/14),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (9*pi/14) (225),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(9 * pi / 14) * sin(-pi / 7) + cos(9 * pi / 14) * cos(-pi / 7) = cos(-pi/7)*cos(9*pi/14) - sin(-pi/7)*sin(9*pi/14),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(9*pi/14) * sin(-pi/7) + cos(9*pi/14) * cos(-pi/7),
{
have : cos(pi/2) = cos((9*pi/14) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_number_generalization_step2_534 : sin(3655*pi)=0:=
begin
have : - -sin(3655 * pi) = sin(3655*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1752*pi) = -sin(3655*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1752*pi) (951),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(1752*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (875),
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


lemma Trigo_number_generalization_step2_535 (h0 : cos(3*pi/4)≠ 0) (h1 : sin(7519*pi/4)≠ 0) : sin(3*pi/4)/sin(7519*pi/4)=- 1:=
begin
have : cos(3*pi/4) = sin(7519*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (940),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = sin(3*pi/4) / cos(3*pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_536 : -sin(-8053*pi/6)=sin(6085*pi/6):=
begin
have : -sin((-8053) * pi / 6) = -sin(-8053*pi/6),
{
field_simp at *,
},
have : sin(11737*pi/6) = -sin(-8053*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (11737*pi/6) (307),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(11737*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (978),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(6085*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (507),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_537 (h0 : cos((pi/3)/2)≠ 0) (h1 : (cos(pi/3)+1)≠ 0) (h2 : (1+cos(pi/3))≠ 0) (h3 : (sin(-pi/5)*sin(2*pi/15)+cos(-pi/5)*cos(2*pi/15)+1)≠ 0) (h4 : (sin(2*pi/15)*sin(-pi/5)+cos(2*pi/15)*cos(-pi/5)+1)≠ 0) : sin(pi/3)/(sin(-pi/5)*sin(2*pi/15) + cos(-pi/5)*cos(2*pi/15) + 1)=sqrt( 3 ) / 3:=
begin
have : sin(pi / 3) / (sin(2 * pi / 15) * sin(-pi / 5) + cos(2 * pi / 15) * cos(-pi / 5) + 1) = sin(pi/3)/(sin(-pi/5)*sin(2*pi/15) + cos(-pi/5)*cos(2*pi/15) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(2*pi/15) * sin(-pi/5) + cos(2*pi/15) * cos(-pi/5),
{
have : cos(pi/3) = cos((2*pi/15) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_538 : -cos(15131*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(1799*pi/12) = -cos(15131*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (1799*pi/12) (555),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = cos(1799*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/12) (75),
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


lemma Trigo_number_generalization_step2_539 (h0 : sin(1222*pi/3)≠ 0) (h1 : (2*sin(1222*pi/3))≠ 0) : -sin(2444*pi/3)/(2*sin(1222*pi/3))=1 / 2:=
begin
have : -(sin(2444 * pi / 3) / (2 * sin(1222 * pi / 3))) = -sin(2444*pi/3)/(2*sin(1222*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1222*pi/3) = sin(2444*pi/3) / ( 2 * sin(1222*pi/3) ),
{
have : sin(2444*pi/3) = sin(2*(1222*pi/3)),
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
have : sin(pi/6) = -cos(1222*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (203),
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


lemma Trigo_number_generalization_step2_540 : sin(346*pi/5)*sin(2956*pi/3)=sin(11*pi/30) / 2 + sin(pi/30) / 2:=
begin
have : -sin(346 * pi / 5) * -sin(2956 * pi / 3) = sin(346*pi/5)*sin(2956*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(2956*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (492),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = -sin(346*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/5) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) * cos(-pi/6) = sin(11*pi/30) / 2 + sin(pi/30) / 2,
{
rw sin_mul_cos,
have : sin((pi/5) + (-pi/6)) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (-pi/6)) = sin(11*pi/30),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_541 : sin(1625*pi)=-1 + 2*sin(3877*pi/4)**2:=
begin
have : sin(-2*pi) = sin(1625*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (811),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - 2 * sin(3877 * pi / 4) ** 2) = -1 + 2*sin(3877*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3877*pi/2) = 1 - 2 * sin(3877*pi/4) ** 2,
{
have : cos(3877*pi/2) = cos(2*(3877*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = - cos(3877*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (970),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_542 (h0 : cos(3*pi/8)≠ 0) (h1 : (1-tan(3*pi/8)**2)≠ 0) (h2 : cos((3*pi/4)/2)≠ 0) (h3 : ((-(1-cos(3*pi/4))**2/sin(3*pi/4)**2+1)*sin(3*pi/4))≠ 0) (h4 : (1-((1-cos(3*pi/4))/sin(3*pi/4))**2)≠ 0) (h5 : sin(3*pi/4)≠ 0) : 2*(1 - cos(3*pi/4))/((-(1 - cos(3*pi/4))**2/sin(3*pi/4)**2 + 1)*sin(3*pi/4))=- 1:=
begin
have : 2 * ((1 - cos(3 * pi / 4)) / sin(3 * pi / 4)) / (1 - ((1 - cos(3 * pi / 4)) / sin(3 * pi / 4)) ** 2) = 2*(1 - cos(3*pi/4))/((-(1 - cos(3*pi/4))**2/sin(3*pi/4)**2 + 1)*sin(3*pi/4)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/8) = ( 1 - cos(3*pi/4) ) / sin(3*pi/4),
{
have : tan(3*pi/8) = tan((3*pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 2 * tan(3*pi/8) / ( 1 - tan(3*pi/8) ** 2 ),
{
have : tan(3*pi/4) = tan(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_543 : -1 + 2*sin(3267*pi/4)**2=0:=
begin
have : -(1 - 2 * sin(3267 * pi / 4) ** 2) = -1 + 2*sin(3267*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3267*pi/2) = 1 - 2 * sin(3267*pi/4) ** 2,
{
have : cos(3267*pi/2) = cos(2*(3267*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(3267*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (816),
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


lemma Trigo_number_generalization_step2_544 : 1 - 2*cos(4073*pi/12)**2=cos(5099*pi/6):=
begin
have : -(2 * cos(4073 * pi / 12) ** 2 - 1) = 1 - 2*cos(4073*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(4073*pi/6) = 2 * cos(4073*pi/12) ** 2 - 1,
{
have : cos(4073*pi/6) = cos(2*(4073*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(4073*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (339),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(5099*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (425),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_545 : -1 + 2*sin(4969*pi/3)**2=- cos(3976*pi/3):=
begin
have : cos(pi/6) = sin(4969*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (828),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 6) ** 2 - 1 = -1 + 2*cos(pi/6)**2,
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
have : cos(pi/3) = - cos(3976*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (662),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_546 : -sin(pi/8)*sin(6327*pi/8) - cos(pi/8)*cos(6327*pi/8)=2 * cos(-pi/8) ** 2 - 1:=
begin
have : -(sin(6327 * pi / 8) * sin(pi / 8) + cos(6327 * pi / 8) * cos(pi / 8)) = -sin(pi/8)*sin(6327*pi/8) - cos(pi/8)*cos(6327*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3163*pi/4) = sin(6327*pi/8) * sin(pi/8) + cos(6327*pi/8) * cos(pi/8),
{
have : cos(3163*pi/4) = cos((6327*pi/8) - (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -cos(3163*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/4) (395),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = 2 * cos(-pi/8) ** 2 - 1,
{
have : cos(-pi/4) = cos(2*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_547 : cos(5263*pi/4)=cos(9135*pi/4):=
begin
have : - -cos(9135 * pi / 4) = cos(9135*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1989*pi/4) = -cos(9135*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1989*pi/4) (893),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = cos(5263*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/4) (658),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - sin(1989*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (248),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_548 : -(-sin(pi)*cos(7*pi/6) + sin(7*pi/6)*cos(pi))*sin(-13*pi/6) + cos(-13*pi/6)*cos(pi/6)=2 * cos(-pi) ** 2 - 1:=
begin
have : -sin((-13) * pi / 6) * (sin(7 * pi / 6) * cos(pi) - sin(pi) * cos(7 * pi / 6)) + cos((-13) * pi / 6) * cos(pi / 6) = -(-sin(pi)*cos(7*pi/6) + sin(7*pi/6)*cos(pi))*sin(-13*pi/6) + cos(-13*pi/6)*cos(pi/6),
{
field_simp at *,
ring,
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
have : -sin((-13) * pi / 6) * sin(pi / 6) + cos((-13) * pi / 6) * cos(pi / 6) = -sin(-13*pi/6)*sin(pi/6) + cos(-13*pi/6)*cos(pi/6),
{
field_simp at *,
},
have : cos(-2*pi) = -sin(-13*pi/6) * sin(pi/6) + cos(-13*pi/6) * cos(pi/6),
{
have : cos(-2*pi) = cos((-13*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_number_generalization_step2_549 : 3*cos(4886*pi/27) - cos(-pi/8) - 4*cos(4886*pi/27)**3=- 2 * sin(pi/144) * sin(-17*pi/144):=
begin
have : (-3) * -cos(4886 * pi / 27) - cos(-pi / 8) + 4 * (-cos(4886 * pi / 27)) ** 3 = 3*cos(4886*pi/27) - cos(-pi/8) - 4*cos(4886*pi/27)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/27) = -cos(4886*pi/27),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/27) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(-pi / 27) ** 3 - 3 * cos(-pi / 27) - cos(-pi / 8) = -3*cos(-pi/27) - cos(-pi/8) + 4*cos(-pi/27)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = 4 * cos(-pi/27) ** 3 - 3 * cos(-pi/27),
{
have : cos(-pi/9) = cos(3*(-pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) - cos(-pi/8) = - 2 * sin(pi/144) * sin(-17*pi/144),
{
rw cos_sub_cos,
have : sin(((-pi/9) + (-pi/8))/2) = sin(-17*pi/144),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/9) - (-pi/8))/2) = sin(pi/144),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_550 (h0 : cos((4*pi)/2)≠ 0) (h1 : sin(4*pi)≠ 0) (h2 : ((-1)/tan(1558*pi))≠ 0) (h3 : tan(1558*pi)≠ 0) : (1 - cos(4*pi))/sin(4*pi)=-tan(1558*pi):=
begin
have : 1 / ((-1) / tan(1558 * pi)) = -tan(1558*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(1199*pi/2) = -1 / tan(1558*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (1199*pi/2) (958),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : tan(2*pi) = 1 / tan(1199*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (601),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_551 : (sin(3*pi)*cos(pi) + sin(pi)*sin(2421*pi/2))*cos(-pi/8)=- sin(-17*pi/8) / 2 + sin(15*pi/8) / 2:=
begin
have : (sin(3 * pi) * cos(pi) - sin(pi) * -sin(2421 * pi / 2)) * cos(-pi / 8) = (sin(3*pi)*cos(pi) + sin(pi)*sin(2421*pi/2))*cos(-pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = -sin(2421*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi) (606),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(3*pi) * cos(pi) - sin(pi) * cos(3*pi),
{
have : sin(2*pi) = sin((3*pi) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(-pi/8) = - sin(-17*pi/8) / 2 + sin(15*pi/8) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/8) + (2*pi)) = sin(15*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/8) - (2*pi)) = sin(-17*pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_552 : 1 - 2*cos(539*pi)**2=- sin(749*pi/2):=
begin
have : -(2 * cos(539 * pi) ** 2 - 1) = 1 - 2*cos(539*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1078*pi) = 2 * cos(539*pi) ** 2 - 1,
{
have : cos(1078*pi) = cos(2*(539*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(1078*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (538),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(749*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (187),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_553 : sin(2699*pi/6)**2 + cos(-pi/3)/2 + 1/2=1:=
begin
have : sin(-pi/6) = sin(2699*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (225),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 6) ** 2 + (cos(-pi / 3) / 2 + 1 / 2) = sin(-pi/6)**2 + cos(-pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) ** 2 = cos(-pi/3) / 2 + 1 / 2,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) ** 2 + cos(-pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_554 (h0 : cos(13*pi/15)≠ 0) (h1 : cos(pi/5)≠ 0) (h2 : (tan(pi/5)*tan(13*pi/15)+1)≠ 0) (h3 : (1+tan(13*pi/15)*tan(pi/5))≠ 0) (h4 : cos(13*pi/15)≠ 0) (h5 : cos(pi/5)≠ 0) (h6 : 1 + tan(13*pi/15) * tan(pi/5)≠ 0) : tan(2*pi/3)=- sqrt( 3 ):=
begin
have : (tan(13 * pi / 15) * tan(pi / 5) + 1) * tan(2 * pi / 3) / (tan(pi / 5) * tan(13 * pi / 15) + 1) = tan(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(13*pi/15) - tan(pi/5) = ( tan(13*pi/15) * tan(pi/5) + 1 ) * tan(2*pi/3),
{
rw tan_sub_tan,
have : tan((13*pi/15) - (pi/5)) = tan(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(13*pi/15) - tan(pi/5)) = (-tan(pi/5)+tan(13*pi/15)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan(13 * pi / 15) - tan(pi / 5)) / (1 + tan(13 * pi / 15) * tan(pi / 5)) = (-tan(pi/5) + tan(13*pi/15))/(tan(pi/5)*tan(13*pi/15) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = ( tan(13*pi/15) - tan(pi/5) ) / ( 1 + tan(13*pi/15) * tan(pi/5) ),
{
have : tan(2*pi/3) = tan((13*pi/15) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_555 (h0 : cos(2759*pi/6)≠ 0) (h1 : (2*cos(2759*pi/6))≠ 0) : -sin(2759*pi/3)/(2*cos(2759*pi/6))=1 / 2:=
begin
have : -(sin(2759 * pi / 3) / (2 * cos(2759 * pi / 6))) = -sin(2759*pi/3)/(2*cos(2759*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2759*pi/6) = sin(2759*pi/3) / ( 2 * cos(2759*pi/6) ),
{
have : sin(2759*pi/3) = sin(2*(2759*pi/6)),
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
have : sin(pi/6) = -sin(2759*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (230),
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


lemma Trigo_number_generalization_step2_556 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) : (-cos(pi/8)*cos(13*pi/24) + sin(pi/8)*sin(13*pi/24) + 1)/sin(2*pi/3)=sqrt( 3 ):=
begin
have : (1 - (-sin(13 * pi / 24) * sin(pi / 8) + cos(13 * pi / 24) * cos(pi / 8))) / sin(2 * pi / 3) = (-cos(pi/8)*cos(13*pi/24) + sin(pi/8)*sin(13*pi/24) + 1)/sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(13*pi/24) * sin(pi/8) + cos(13*pi/24) * cos(pi/8),
{
have : cos(2*pi/3) = cos((13*pi/24) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( 1 - cos(2*pi/3) ) / sin(2*pi/3),
{
have : tan(pi/3) = tan((2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_557 : -1 + 2*cos(pi/2)**2=cos(-581*pi):=
begin
have : 2 * cos(pi / 2) ** 2 - 1 = -1 + 2*cos(pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 2 * cos(pi/2) ** 2 - 1,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : - -cos((-581) * pi) = cos(-581*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(3861*pi/2) = -cos(-581*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3861*pi/2) (674),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = - sin(3861*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (964),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_558 : (sin(-pi/5)*cos(2*pi/35) + sin(2*pi/35)*cos(-pi/5))*cos(15*pi/7) + sin(15*pi/7)*cos(-pi/7)=sin(1091*pi):=
begin
have : (sin(2 * pi / 35) * cos(-pi / 5) + sin(-pi / 5) * cos(2 * pi / 35)) * cos(15 * pi / 7) + sin(15 * pi / 7) * cos(-pi / 7) = (sin(-pi/5)*cos(2*pi/35) + sin(2*pi/35)*cos(-pi/5))*cos(15*pi/7) + sin(15*pi/7)*cos(-pi/7),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = sin(2*pi/35) * cos(-pi/5) + sin(-pi/5) * cos(2*pi/35),
{
have : sin(-pi/7) = sin((2*pi/35) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(15 * pi / 7) * cos(-pi / 7) + sin(-pi / 7) * cos(15 * pi / 7) = sin(-pi/7)*cos(15*pi/7) + sin(15*pi/7)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(15*pi/7) * cos(-pi/7) + sin(-pi/7) * cos(15*pi/7),
{
have : sin(2*pi) = sin((15*pi/7) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(1091*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (546),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_559 : -sin(-pi/6)*cos(6689*pi/6) + sin(6689*pi/6)*cos(-pi/6)=2 * sin(-pi/2) * cos(-pi/2):=
begin
have : sin(6689 * pi / 6) * cos(-pi / 6) - sin(-pi / 6) * cos(6689 * pi / 6) = -sin(-pi/6)*cos(6689*pi/6) + sin(6689*pi/6)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1115*pi) = sin(6689*pi/6) * cos(-pi/6) - sin(-pi/6) * cos(6689*pi/6),
{
have : sin(1115*pi) = sin((6689*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(1115*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (558),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step2_560 : -3*cos(pi/36)**2 + 3*sin(pi/36)**2 + 4*(-sin(pi/36)**2 + cos(pi/36)**2)**3=sqrt( 3 ) / 2:=
begin
have : (-3) * (-sin(pi / 36) ** 2 + cos(pi / 36) ** 2) + 4 * (-sin(pi / 36) ** 2 + cos(pi / 36) ** 2) ** 3 = -3*cos(pi/36)**2 + 3*sin(pi/36)**2 + 4*(-sin(pi/36)**2 + cos(pi/36)**2)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = -sin(pi/36) ** 2 + cos(pi/36) ** 2,
{
have : cos(pi/18) = cos(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_561 : -cos(3371*pi/6)**2 + sin(3371*pi/6)**2=sin(4019*pi/6):=
begin
have : -(-sin(3371 * pi / 6) ** 2 + cos(3371 * pi / 6) ** 2) = -cos(3371*pi/6)**2 + sin(3371*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3371*pi/3) = -sin(3371*pi/6) ** 2 + cos(3371*pi/6) ** 2,
{
have : cos(3371*pi/3) = cos(2*(3371*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(3371*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (561),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(4019*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (335),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_562 : -cos(7599*pi/4)/2 - cos(-7595*pi/4)/2=- sin(pi/4) / 2 + sin(3*pi/4) / 2:=
begin
have : -(cos((-7595) * pi / 4) / 2 + cos(7599 * pi / 4) / 2) = -cos(7599*pi/4)/2 - cos(-7595*pi/4)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) * cos(7597*pi/4) = cos(-7595*pi/4) / 2 + cos(7599*pi/4) / 2,
{
rw cos_mul_cos,
have : cos((pi/2) + (7597*pi/4)) = cos(7599*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (7597*pi/4)) = cos(-7595*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(cos(pi/2) * cos(7597*pi/4)) = -cos(pi/2)*cos(7597*pi/4),
{
ring,
},
conv {to_lhs, rw this,},
have : -cos(7597 * pi / 4) * cos(pi / 2) = -cos(pi/2)*cos(7597*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(7597*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (949),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) * cos(pi/2) = - sin(pi/4) / 2 + sin(3*pi/4) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/2) + (pi/4)) = sin(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (pi/4)) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_563 : sin(153*pi/10)=sin(-pi/2) * cos(-pi/5) - sin(-pi/5) * cos(-pi/2):=
begin
have : cos(3906*pi/5) = sin(153*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3906*pi/5) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/10) = cos(3906*pi/5),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/10) (390),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/10) = sin(-pi/2) * cos(-pi/5) - sin(-pi/5) * cos(-pi/2),
{
have : sin(-3*pi/10) = sin((-pi/2) - (-pi/5)),
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


lemma Trigo_number_generalization_step2_564 (h0 : cos(-pi/9)≠ 0) (h1 : (2*cos(-pi/18)**2-1)≠ 0) (h2 : (-1+2*cos(-pi/18)**2)≠ 0) : tan(-pi/9)=sin(15454*pi/9)/(-1 + 2*cos(-pi/18)**2):=
begin
have : sin(15454 * pi / 9) / (2 * cos(-pi / 18) ** 2 - 1) = sin(15454*pi/9)/(-1 + 2*cos(-pi/18)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = 2 * cos(-pi/18) ** 2 - 1,
{
have : cos(-pi/9) = cos(2*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = sin(15454*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/9) (858),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/9) = sin(-pi/9) / cos(-pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_565 : -2*sin(pi/8)*sin(2459*pi/8)=sin(761*pi/4):=
begin
have : 2 * sin(pi / 8) * -sin(2459 * pi / 8) = -2*sin(pi/8)*sin(2459*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(2459*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (153),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = 2 * sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(761*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_566 : 1 - cos(1577*pi/14)**2=cos(-2*pi/7) / 2 + 1 / 2:=
begin
have : sin(-pi/7) = cos(1577*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) ** 2 = 1 - sin(-pi/7) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) ** 2 = cos(-2*pi/7) / 2 + 1 / 2,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
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


lemma Trigo_number_generalization_step2_567 : -2*sin(pi/8)*cos(pi/8)*cos(7*pi/12) + sin(7*pi/12)*cos(pi/4)=sqrt( 3 ) / 2:=
begin
have : -(2 * sin(pi / 8) * cos(pi / 8)) * cos(7 * pi / 12) + sin(7 * pi / 12) * cos(pi / 4) = -2*sin(pi/8)*cos(pi/8)*cos(7*pi/12) + sin(7*pi/12)*cos(pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = 2 * sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 12) * cos(pi / 4) - sin(pi / 4) * cos(7 * pi / 12) = -sin(pi/4)*cos(7*pi/12) + sin(7*pi/12)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(7*pi/12) * cos(pi/4) - sin(pi/4) * cos(7*pi/12),
{
have : sin(pi/3) = sin((7*pi/12) - (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_568 : (-sin(-pi/12)**2 + cos(6875*pi/12)**2)*sin(pi/5)=- sin(-11*pi/30) / 2 + sin(pi/30) / 2:=
begin
have : (-sin(-pi / 12) ** 2 + (-cos(6875 * pi / 12)) ** 2) * sin(pi / 5) = (-sin(-pi/12)**2 + cos(6875*pi/12)**2)*sin(pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/12) = -cos(6875*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/12) (286),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 5) * (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/12) ** 2 + cos(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) * cos(-pi/6) = - sin(-11*pi/30) / 2 + sin(pi/30) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/6) + (pi/5)) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (pi/5)) = sin(-11*pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_569 : sin(pi/8)*sin(4261*pi/2)=- sin(15*pi/8) / 2 + sin(17*pi/8) / 2:=
begin
have : cos(372*pi) = sin(4261*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (372*pi) (879),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(372*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (187),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) * cos(2*pi) = - sin(15*pi/8) / 2 + sin(17*pi/8) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((2*pi) + (pi/8)) = sin(17*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (pi/8)) = sin(15*pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_570 (h0 : cos(-pi/3)≠ 0) (h1 : (2*cos(-pi/3))≠ 0) (h2 : (2*cos(-pi/3)**3)≠ 0) : 3*sin(-2*pi/3)/(2*cos(-pi/3)) - sin(-2*pi/3)**3/(2*cos(-pi/3)**3)=- sin(1964*pi):=
begin
have : 3 * (sin((-2) * pi / 3) / (2 * cos(-pi / 3))) - 4 * (sin((-2) * pi / 3) / (2 * cos(-pi / 3))) ** 3 = 3*sin(-2*pi/3)/(2*cos(-pi/3)) - sin(-2*pi/3)**3/(2*cos(-pi/3)**3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-2*pi/3) / ( 2 * cos(-pi/3) ),
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
have : (-4) * sin(-pi / 3) ** 3 + 3 * sin(-pi / 3) = 3*sin(-pi/3) - 4*sin(-pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(1964*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (982),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_571 : -cos(2*pi)*cos(4372*pi/3)=cos(7*pi/3) / 2 + cos(5*pi/3) / 2:=
begin
have : cos(2 * pi) * -cos(4372 * pi / 3) = -cos(2*pi)*cos(4372*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(445*pi/3) = -cos(4372*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (445*pi/3) (654),
focus{repeat {apply congr_arg _}},
simp,
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
conv {to_lhs, rw ← this,},
have : cos(2*pi) * cos(-pi/3) = cos(7*pi/3) / 2 + cos(5*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((2*pi) + (-pi/3)) = cos(5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (-pi/3)) = cos(7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_572 : 3*cos(487*pi/18) - 4*cos(487*pi/18)**3=sqrt( 3 ) / 2:=
begin
have : -(4 * cos(487 * pi / 18) ** 3 - 3 * cos(487 * pi / 18)) = 3*cos(487*pi/18) - 4*cos(487*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(487*pi/6) = 4 * cos(487*pi/18) ** 3 - 3 * cos(487*pi/18),
{
have : cos(487*pi/6) = cos(3*(487*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -cos(487*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (40),
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


lemma Trigo_number_generalization_step2_573 : -2*sin(-pi)*cos(1712*pi)=- sin(1478*pi):=
begin
have : 2 * sin(-pi) * -cos(1712 * pi) = -2*sin(-pi)*cos(1712*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -cos(1712*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (856),
focus{repeat {apply congr_arg _}},
simp,
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
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(1478*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (738),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_574 (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : cos(7259*pi/6)/(2*cos(pi/3))=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(7259*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (605),
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
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_575 : (-cos(94*pi)**2 + cos(pi/2)**2)*cos(pi/4)=cos(3*pi/4) / 2 + cos(5*pi/4) / 2:=
begin
have : sin(pi/2) = cos(94*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi) * cos(pi/4) = cos(3*pi/4) / 2 + cos(5*pi/4) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (pi/4)) = cos(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (pi/4)) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_576 (h0 : cos((-pi/3)/2)≠ 0) (h1 : sin(-pi/3)≠ 0) (h2 : (3*sin(-pi/9)-4*sin(-pi/9)**3)≠ 0) (h3 : ((-4)*sin(-pi/9)**3+3*sin(-pi/9))≠ 0) : (1 - cos(-pi/3))/(3*sin(-pi/9) - 4*sin(-pi/9)**3)=- tan(4915*pi/6):=
begin
have : (1 - cos(-pi / 3)) / ((-4) * sin(-pi / 9) ** 3 + 3 * sin(-pi / 9)) = (1 - cos(-pi/3))/(3*sin(-pi/9) - 4*sin(-pi/9)**3),
{
field_simp at *,
repeat {left},
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
have : tan(-pi/6) = ( 1 - cos(-pi/3) ) / sin(-pi/3),
{
have : tan(-pi/6) = tan((-pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - tan(4915*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/6) (819),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_577 : -sin(2066*pi)=- 4 * sin(pi/3) ** 3 + 3 * sin(pi/3):=
begin
have : sin(675*pi) = -sin(2066*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (675*pi) (695),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(675*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (337),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - 4 * sin(pi/3) ** 3 + 3 * sin(pi/3),
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
rw this,
end


lemma Trigo_number_generalization_step2_578 : -2*sin(521*pi/6)*cos(521*pi/6)=sqrt( 3 ) / 2:=
begin
have : -(2 * sin(521 * pi / 6) * cos(521 * pi / 6)) = -2*sin(521*pi/6)*cos(521*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(521*pi/3) = 2 * sin(521*pi/6) * cos(521*pi/6),
{
have : sin(521*pi/3) = sin(2*(521*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(521*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (86),
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


lemma Trigo_number_generalization_step2_579 : cos(-pi/8)*cos(17*pi/24) + sin(17*pi/24)*sin(4313*pi/8)=- sqrt( 3 ) / 2:=
begin
have : cos(-pi / 8) * cos(17 * pi / 24) + sin(4313 * pi / 8) * sin(17 * pi / 24) = cos(-pi/8)*cos(17*pi/24) + sin(17*pi/24)*sin(4313*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(4313*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/8) (269),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17 * pi / 24) * sin(-pi / 8) + cos(17 * pi / 24) * cos(-pi / 8) = cos(-pi/8)*cos(17*pi/24) + sin(-pi/8)*sin(17*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = sin(17*pi/24) * sin(-pi/8) + cos(17*pi/24) * cos(-pi/8),
{
have : cos(5*pi/6) = cos((17*pi/24) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_580 (h0 : cos(pi/3)≠ 0) : (-4*sin(pi/9)**3 + 3*sin(pi/9))/cos(pi/3)=sqrt( 3 ):=
begin
have : ((-4) * sin(pi / 9) ** 3 + 3 * sin(pi / 9)) / cos(pi / 3) = (-4*sin(pi/9)**3 + 3*sin(pi/9))/cos(pi/3),
{
field_simp at *,
},
have : sin(pi/3) = -4 * sin(pi/9) ** 3 + 3 * sin(pi/9),
{
have : sin(pi/3) = sin(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_581 : -cos(4753*pi/3)=- 1 / 2:=
begin
have : sin(6671*pi/6) = -cos(4753*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (6671*pi/6) (236),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(6671*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (556),
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


lemma Trigo_number_generalization_step2_582 : -1 + 2*sin(958*pi)**2=- 1:=
begin
have : -(1 - 2 * sin(958 * pi) ** 2) = -1 + 2*sin(958*pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1916*pi) = 1 - 2 * sin(958*pi) ** 2,
{
have : cos(1916*pi) = cos(2*(958*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(1916*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (957),
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


lemma Trigo_number_generalization_step2_583 : sin(12370*pi/7)=- sin(3786*pi/7):=
begin
have : - -sin(12370 * pi / 7) = sin(12370*pi/7),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(4369*pi/7) = -sin(12370*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4369*pi/7) (571),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = -sin(4369*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/7) (312),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = - sin(3786*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/7) (270),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_584 : -cos(-pi/7)*cos(13803*pi/7) - sin(-pi/7)*sin(13803*pi/7)=cos(517*pi):=
begin
have : -(sin(13803 * pi / 7) * sin(-pi / 7) + cos(13803 * pi / 7) * cos(-pi / 7)) = -cos(-pi/7)*cos(13803*pi/7) - sin(-pi/7)*sin(13803*pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1972*pi) = sin(13803*pi/7) * sin(-pi/7) + cos(13803*pi/7) * cos(-pi/7),
{
have : cos(1972*pi) = cos((13803*pi/7) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(1972*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (985),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(517*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (258),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_585 : 1 - 2*cos(247*pi/6)**2=sin(6647*pi/6):=
begin
have : -(2 * cos(247 * pi / 6) ** 2 - 1) = 1 - 2*cos(247*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(247*pi/3) = 2 * cos(247*pi/6) ** 2 - 1,
{
have : cos(247*pi/3) = cos(2*(247*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(247*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(6647*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (554),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_586 : sin(2281*pi/2)=-cos(1585*pi):=
begin
have : cos(1038*pi) = -cos(1585*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (1038*pi) (273),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(2281*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (569),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(1038*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (518),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_587 (h0 : tan(5131*pi/6)≠ 0) (h1 : tan(10027*pi/6)≠ 0) : 1/tan(10027*pi/6)=sqrt( 3 ):=
begin
have : tan(5131*pi/6) = tan(10027*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (5131*pi/6) (816),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(5131*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (855),
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


lemma Trigo_number_generalization_step2_588 : (-sin(3*pi/28)*sin(2375*pi/4) + cos(-pi/4)*cos(3*pi/28))*sin(-2*pi)=sin(-13*pi/7) / 2 + sin(-15*pi/7) / 2:=
begin
have : (-sin(2375 * pi / 4) * sin(3 * pi / 28) + cos(-pi / 4) * cos(3 * pi / 28)) * sin((-2) * pi) = (-sin(3*pi/28)*sin(2375*pi/4) + cos(-pi/4)*cos(3*pi/28))*sin(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(2375*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/4) (297),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi) * (-sin(3 * pi / 28) * sin(-pi / 4) + cos(3 * pi / 28) * cos(-pi / 4)) = (-sin(-pi/4)*sin(3*pi/28) + cos(-pi/4)*cos(3*pi/28))*sin(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = -sin(3*pi/28) * sin(-pi/4) + cos(3*pi/28) * cos(-pi/4),
{
have : cos(-pi/7) = cos((3*pi/28) + (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/7) = sin(-13*pi/7) / 2 + sin(-15*pi/7) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-pi/7)) = sin(-15*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-pi/7)) = sin(-13*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_589 : sin(1960*pi)=- sin(1822*pi):=
begin
have : - -sin(1960 * pi) = sin(1960*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1361*pi) = -sin(1960*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1361*pi) (299),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(1361*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (681),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(1822*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (910),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_590 (h0 : sin(pi/5)≠ 0) (h1 : (2*sin(pi/5))≠ 0) : sin(-pi/30)*sin(2*pi/5)/(2*sin(pi/5)) + sin(pi/5)*cos(-pi/30)=1 / 2:=
begin
have : sin(-pi / 30) * (sin(2 * pi / 5) / (2 * sin(pi / 5))) + sin(pi / 5) * cos(-pi / 30) = sin(-pi/30)*sin(2*pi/5)/(2*sin(pi/5)) + sin(pi/5)*cos(-pi/30),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = sin(2*pi/5) / ( 2 * sin(pi/5) ),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
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
have : sin(pi/6) = sin(-pi/30) * cos(pi/5) + sin(pi/5) * cos(-pi/30),
{
have : sin(pi/6) = sin((-pi/30) + (pi/5)),
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


lemma Trigo_number_generalization_step2_591 (h0 : tan(2353*pi/6)≠ 0) (h1 : cos(2353*pi/12)≠ 0) (h2 : (1-tan(2353*pi/12)**2)≠ 0) (h3 : (2*tan(2353*pi/12)/(1-tan(2353*pi/12)**2))≠ 0) (h4 : (2*tan(2353*pi/12))≠ 0) : (1 - tan(2353*pi/12)**2)/(2*tan(2353*pi/12))=sqrt( 3 ):=
begin
have : 1 / (2 * tan(2353 * pi / 12) / (1 - tan(2353 * pi / 12) ** 2)) = (1 - tan(2353*pi/12)**2)/(2*tan(2353*pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2353*pi/6) = 2 * tan(2353*pi/12) / ( 1 - tan(2353*pi/12) ** 2 ),
{
have : tan(2353*pi/6) = tan(2*(2353*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(2353*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (392),
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


lemma Trigo_number_generalization_step2_592 (h0 : cos(2*pi/3)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(-pi/3)*tan(2*pi/3))≠ 0) (h3 : (1+tan(2*pi/3)*tan(-pi/3))≠ 0) (h4 : tan(4375*pi/6)≠ 0) (h5 : (1-tan(2*pi/3)/tan(4375*pi/6))≠ 0) (h6 : (1+(-1)/tan(4375*pi/6)*tan(2*pi/3))≠ 0) : (tan(2*pi/3) + 1/tan(4375*pi/6))/(1 - tan(2*pi/3)/tan(4375*pi/6))=0:=
begin
have : (tan(2 * pi / 3) - (-1) / tan(4375 * pi / 6)) / (1 + (-1) / tan(4375 * pi / 6) * tan(2 * pi / 3)) = (tan(2*pi/3) + 1/tan(4375*pi/6))/(1 - tan(2*pi/3)/tan(4375*pi/6)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = -1 / tan(4375*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (729),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(2 * pi / 3) - tan(-pi / 3)) / (1 + tan(2 * pi / 3) * tan(-pi / 3)) = (tan(2*pi/3) - tan(-pi/3))/(1 + tan(-pi/3)*tan(2*pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(2*pi/3) - tan(-pi/3) ) / ( 1 + tan(2*pi/3) * tan(-pi/3) ),
{
have : tan(pi) = tan((2*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_593 : 4*cos(3931*pi/6)**3 - 3*cos(3931*pi/6)=- sin(1324*pi):=
begin
have : cos(3931*pi/2) = 4 * cos(3931*pi/6) ** 3 - 3 * cos(3931*pi/6),
{
have : cos(3931*pi/2) = cos(3*(3931*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(3931*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (982),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(1324*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (662),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_594 : sin(-11845*pi/6)/2 + sin(11839*pi/6)/2=- sin(pi/6) / 2 + sin(-5*pi/6) / 2:=
begin
have : sin((-11845) * pi / 6) / 2 + sin(11839 * pi / 6) / 2 = sin(-11845*pi/6)/2 + sin(11839*pi/6)/2,
{
field_simp at *,
},
have : sin(-pi/2) * cos(5921*pi/3) = sin(-11845*pi/6) / 2 + sin(11839*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-pi/2) + (5921*pi/3)) = sin(11839*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (5921*pi/3)) = sin(-11845*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi/2) * cos(5921*pi/3)) = sin(-pi/2)*cos(5921*pi/3),
{
ring,
},
have : cos(-pi/3) = cos(5921*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (987),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(-pi/3) = - sin(pi/6) / 2 + sin(-5*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/3) + (-pi/2)) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/3) - (-pi/2)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_595 : -1 + 2*cos(119*pi/2)**2=- 1:=
begin
have : -1 + 2 * (-cos(119 * pi / 2)) ** 2 = -1 + 2*cos(119*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(119*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 2) ** 2 - 1 = -1 + 2*cos(pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = 2 * cos(pi/2) ** 2 - 1,
{
have : cos(pi) = cos(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_596 (h0 : cos(385*pi/3)≠ 0) (h1 : cos(pi/2)≠ 0) (h2 : (1+tan(385*pi/3)*tan(pi/2))≠ 0) (h3 : (1+tan(pi/2)*tan(385*pi/3))≠ 0) : -(-tan(pi/2) + tan(385*pi/3))/(1 + tan(pi/2)*tan(385*pi/3))=sqrt( 3 ) / 3:=
begin
have : -((tan(385 * pi / 3) - tan(pi / 2)) / (1 + tan(385 * pi / 3) * tan(pi / 2))) = -(-tan(pi/2) + tan(385*pi/3))/(1 + tan(pi/2)*tan(385*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(767*pi/6) = ( tan(385*pi/3) - tan(pi/2) ) / ( 1 + tan(385*pi/3) * tan(pi/2) ),
{
have : tan(767*pi/6) = tan((385*pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(767*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (128),
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


lemma Trigo_number_generalization_step2_597 : sin(pi) * sin(-pi/7)=-sin(3309*pi/14)/2 - sin(pi)*sin(13*pi/7)/2 - cos(pi)*cos(13*pi/7)/2:=
begin
have : cos(8*pi/7) = -sin(3309*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/7) (118),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(8 * pi / 7) / 2 - (sin(13 * pi / 7) * sin(pi) + cos(13 * pi / 7) * cos(pi)) / 2 = cos(8*pi/7)/2 - sin(pi)*sin(13*pi/7)/2 - cos(pi)*cos(13*pi/7)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(6*pi/7) = sin(13*pi/7) * sin(pi) + cos(13*pi/7) * cos(pi),
{
have : cos(6*pi/7) = cos((13*pi/7) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * sin(-pi/7) = cos(8*pi/7) / 2 - cos(6*pi/7) / 2,
{
rw sin_mul_sin,
have : cos((pi) + (-pi/7)) = cos(6*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (-pi/7)) = cos(8*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_598 : -sin(26639*pi/20)*cos(pi/5) + sin(pi/5)*sin(9*pi/20)=- cos(2213*pi/4):=
begin
have : cos(pi / 5) * -sin(26639 * pi / 20) + sin(pi / 5) * sin(9 * pi / 20) = -sin(26639*pi/20)*cos(pi/5) + sin(pi/5)*sin(9*pi/20),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(9*pi/20) = -sin(26639*pi/20),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (9*pi/20) (665),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(9 * pi / 20) * sin(pi / 5) + cos(9 * pi / 20) * cos(pi / 5) = cos(pi/5)*cos(9*pi/20) + sin(pi/5)*sin(9*pi/20),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(9*pi/20) * sin(pi/5) + cos(9*pi/20) * cos(pi/5),
{
have : cos(pi/4) = cos((9*pi/20) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = - cos(2213*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (276),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_599 (h0 : tan(2767*pi/4)≠ 0) (h1 : ((-1)/tan(4325*pi/4))≠ 0) (h2 : tan(4325*pi/4)≠ 0) : tan(4325*pi/4)=1:=
begin
have : (-1) / ((-1) / tan(4325 * pi / 4)) = tan(4325*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2767*pi/4) = -1 / tan(4325*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2767*pi/4) (389),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(2767 * pi / 4) = -1/tan(2767*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(2767*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (691),
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


lemma Trigo_number_generalization_step2_600 : -cos(-pi/6) + sin(pi/9)*sin(19*pi/9) + cos(pi/9)*cos(19*pi/9)=2*sin(13*pi/12)*cos(1135*pi/12):=
begin
have : sin(19 * pi / 9) * sin(pi / 9) + cos(19 * pi / 9) * cos(pi / 9) - cos(-pi / 6) = -cos(-pi/6) + sin(pi/9)*sin(19*pi/9) + cos(pi/9)*cos(19*pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(19*pi/9) * sin(pi/9) + cos(19*pi/9) * cos(pi/9),
{
have : cos(2*pi) = cos((19*pi/9) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * sin(13 * pi / 12) * -cos(1135 * pi / 12) = 2*sin(13*pi/12)*cos(1135*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(11*pi/12) = -cos(1135*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (11*pi/12) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) - cos(-pi/6) = - 2 * sin(13*pi/12) * sin(11*pi/12),
{
rw cos_sub_cos,
have : sin(((2*pi) + (-pi/6))/2) = sin(11*pi/12),
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_601 (h0 : cos(pi/3)≠ 0) (h1 : cos(pi/4)≠ 0) (h2 : (1+tan(pi/3)*tan(pi/4))≠ 0) (h3 : (1+tan(pi/4)*tan(pi/3))≠ 0) (h4 : cos(pi/4)≠ 0) (h5 : cos(pi/3)≠ 0) (h6 : tan((pi/4)-(pi/3))≠ 0) (h7 : 1+tan(pi/4)*tan(pi/3)≠ 0) (h8 : tan(-pi/12)≠ 0) (h9 : (1+((tan(pi/4)-tan(pi/3))/tan(-pi/12)-1))≠ 0) (h10 : (-tan(pi/3)+tan(pi/4))≠ 0) : (-tan(pi/4) + tan(pi/3))*tan(-pi/12)/(-tan(pi/3) + tan(pi/4))=2 - sqrt( 3 ):=
begin
have : (-tan(pi / 4) + tan(pi / 3)) / (1 + ((tan(pi / 4) - tan(pi / 3)) / tan(-pi / 12) - 1)) = (-tan(pi/4) + tan(pi/3))*tan(-pi/12)/(-tan(pi/3) + tan(pi/4)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) * tan(pi/3) = ( tan(pi/4) - tan(pi/3) ) / tan(-pi/12) - 1,
{
rw tan_mul_tan,
have : tan((pi/4) - (pi/3)) = tan(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(pi/4) * tan(pi/3)) = tan(pi/4)*tan(pi/3),
{
ring,
},
have : (tan(pi / 3) - tan(pi / 4)) / (1 + tan(pi / 3) * tan(pi / 4)) = (-tan(pi/4) + tan(pi/3))/(1 + tan(pi/4)*tan(pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(pi/3) - tan(pi/4) ) / ( 1 + tan(pi/3) * tan(pi/4) ),
{
have : tan(pi/12) = tan((pi/3) - (pi/4)),
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


lemma Trigo_number_generalization_step2_602 : -sin(-pi/6)*sin(4708*pi/3) - cos(-pi/6)*cos(4708*pi/3)=- sin(1223*pi):=
begin
have : -(sin(4708 * pi / 3) * sin(-pi / 6) + cos(4708 * pi / 3) * cos(-pi / 6)) = -sin(-pi/6)*sin(4708*pi/3) - cos(-pi/6)*cos(4708*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3139*pi/2) = sin(4708*pi/3) * sin(-pi/6) + cos(4708*pi/3) * cos(-pi/6),
{
have : cos(3139*pi/2) = cos((4708*pi/3) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -cos(3139*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (783),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(1223*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (612),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_603 : -cos(-pi/4)*cos(1489*pi/4) - sin(-pi/4)*sin(1489*pi/4)=cos(1327*pi/2):=
begin
have : -(sin(1489 * pi / 4) * sin(-pi / 4) + cos(1489 * pi / 4) * cos(-pi / 4)) = -cos(-pi/4)*cos(1489*pi/4) - sin(-pi/4)*sin(1489*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(745*pi/2) = sin(1489*pi/4) * sin(-pi/4) + cos(1489*pi/4) * cos(-pi/4),
{
have : cos(745*pi/2) = cos((1489*pi/4) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -cos(745*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (186),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(1327*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (332),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_604 : -sin(705*pi/2)=-1 + 2*(cos(-5*pi/8)*cos(-pi/8) + sin(-5*pi/8)*sin(-pi/8))**2:=
begin
have : 2 * (sin((-5) * pi / 8) * sin(-pi / 8) + cos((-5) * pi / 8) * cos(-pi / 8)) ** 2 - 1 = -1 + 2*(cos(-5*pi/8)*cos(-pi/8) + sin(-5*pi/8)*sin(-pi/8))**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(-5*pi/8) * sin(-pi/8) + cos(-5*pi/8) * cos(-pi/8),
{
have : cos(-pi/2) = cos((-5*pi/8) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -sin(705*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (175),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_number_generalization_step2_605 : cos(-2*pi/9)=1 - 2*cos(10253*pi/18)**2:=
begin
have : 1 - 2 * (-cos(10253 * pi / 18)) ** 2 = 1 - 2*cos(10253*pi/18)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(8999*pi/9) = -cos(10253*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8999*pi/9) (784),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = sin(8999*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/9) (500),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/9) = 1 - 2 * sin(-pi/9) ** 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_606 (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) (h2 : cos(3619*pi/2)≠ 0) (h3 : -cos(3619*pi/2)≠ 0) : -(1 - cos(2*pi))/cos(3619*pi/2)=0:=
begin
have : (1 - cos(2 * pi)) / -cos(3619 * pi / 2) = -(1 - cos(2*pi))/cos(3619*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(3619*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (905),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_607 : tan(839*pi/5)=1 / tan(4107*pi/10):=
begin
have : - -tan(839 * pi / 5) = tan(839*pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(251*pi/5) = -tan(839*pi/5),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (251*pi/5) (218),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = -tan(251*pi/5),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/5) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = 1 / tan(4107*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/5) (410),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_608 : -cos(-4135*pi/6)=cos(10129*pi/6):=
begin
have : -cos((-4135) * pi / 6) = -cos(-4135*pi/6),
{
field_simp at *,
},
have : cos(5461*pi/6) = -cos(-4135*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5461*pi/6) (110),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(5461*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (455),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(10129*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (844),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_609 : 2*(-3*cos(-pi/6) + 4*cos(-pi/6)**3)*sin(-pi/2)=sin(930*pi):=
begin
have : 2 * sin(-pi / 2) * (4 * cos(-pi / 6) ** 3 - 3 * cos(-pi / 6)) = 2*(-3*cos(-pi/6) + 4*cos(-pi/6)**3)*sin(-pi/2),
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
have : sin(-pi) = sin(930*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi) (464),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_610 : 2*sin(-7*pi/48)*cos(pi/48)=-2*sin(-7*pi/48)*cos(61775*pi/48):=
begin
have : 2 * sin((-7) * pi / 48) * cos(pi / 48) = 2*sin(-7*pi/48)*cos(pi/48),
{
field_simp at *,
},
have : sin(-pi/8) + sin(-pi/6) = 2 * sin(-7*pi/48) * cos(pi/48),
{
rw sin_add_sin,
have : sin(((-pi/8) + (-pi/6))/2) = sin(-7*pi/48),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/8) - (-pi/6))/2) = cos(pi/48),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi/8) + sin(-pi/6)) = sin(-pi/6)+sin(-pi/8),
{
ring,
},
conv {to_lhs, rw this,},
have : 2 * sin((-7) * pi / 48) * -cos(61775 * pi / 48) = -2*sin(-7*pi/48)*cos(61775*pi/48),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/48) = -cos(61775*pi/48),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/48) (643),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) + sin(-pi/8) = 2 * sin(-7*pi/48) * cos(-pi/48),
{
rw sin_add_sin,
have : sin(((-pi/6) + (-pi/8))/2) = sin(-7*pi/48),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (-pi/8))/2) = cos(-pi/48),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_611 : -cos(2618*pi/9)=-sin(pi)*cos(26507*pi/18) - sin(26507*pi/18)*cos(pi):=
begin
have : -(sin(26507 * pi / 18) * cos(pi) + sin(pi) * cos(26507 * pi / 18)) = -sin(pi)*cos(26507*pi/18) - sin(26507*pi/18)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(26525*pi/18) = sin(26507*pi/18) * cos(pi) + sin(pi) * cos(26507*pi/18),
{
have : sin(26525*pi/18) = sin((26507*pi/18) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = -cos(2618*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/9) (145),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = - sin(26525*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (736),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_612 : cos(14721*pi/8)=-4*sin(9509*pi/24)**3 + 3*sin(9509*pi/24):=
begin
have : (-4) * sin(9509 * pi / 24) ** 3 + 3 * sin(9509 * pi / 24) = -4*sin(9509*pi/24)**3 + 3*sin(9509*pi/24),
{
field_simp at *,
},
have : sin(9509*pi/8) = -4 * sin(9509*pi/24) ** 3 + 3 * sin(9509*pi/24),
{
have : sin(9509*pi/8) = sin(3*(9509*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = cos(14721*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/8) (920),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = sin(9509*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/8) (594),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_613 : cos(12961*pi/6)=cos(2315*pi/6):=
begin
have : - -cos(12961 * pi / 6) = cos(12961*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(7147*pi/6) = -cos(12961*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (7147*pi/6) (484),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(7147*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (595),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(2315*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (192),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_614 : sin(-10301*pi/6)**2=1 - cos(-pi/6) ** 2:=
begin
have : (-sin((-10301) * pi / 6)) ** 2 = sin(-10301*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(10613*pi/6) = -sin(-10301*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (10613*pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(10613 * pi / 6)) ** 2 = sin(10613*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(10613*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (884),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) ** 2 = 1 - cos(-pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_615 : -3*sin(5671*pi/21) + 4*sin(5671*pi/21)**3=sin(13901*pi/7):=
begin
have : 3 * -sin(5671 * pi / 21) - 4 * (-sin(5671 * pi / 21)) ** 3 = -3*sin(5671*pi/21) + 4*sin(5671*pi/21)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/21) = -sin(5671*pi/21),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/21) (135),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(-pi / 21) ** 3 + 3 * sin(-pi / 21) = 3*sin(-pi/21) - 4*sin(-pi/21)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = -4 * sin(-pi/21) ** 3 + 3 * sin(-pi/21),
{
have : sin(-pi/7) = sin(3*(-pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = sin(13901*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/7) (993),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_616 : sin(10052*pi/9)**2=1 - cos(1970*pi/9)**2:=
begin
have : (-sin(10052 * pi / 9)) ** 2 = sin(10052*pi/9)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = -sin(10052*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (558),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (-cos(1970 * pi / 9)) ** 2 = 1 - cos(1970*pi/9)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = -cos(1970*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/9) (109),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) ** 2 = 1 - cos(-pi/9) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_617 : cos(pi/2)*cos(599*pi) - sin(pi/2)*cos(3*pi/2)=- cos(1637*pi/2):=
begin
have : cos(599 * pi) * cos(pi / 2) - sin(pi / 2) * cos(3 * pi / 2) = cos(pi/2)*cos(599*pi) - sin(pi/2)*cos(3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/2) = cos(599*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/2) (298),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(3*pi/2) * cos(pi/2) - sin(pi/2) * cos(3*pi/2),
{
have : sin(pi) = sin((3*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - cos(1637*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (409),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_618 : -sin(-11*pi/12)*cos(1775*pi/2) + cos(-pi)*cos(-11*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -cos(1775 * pi / 2) * sin((-11) * pi / 12) + cos(-pi) * cos((-11) * pi / 12) = -sin(-11*pi/12)*cos(1775*pi/2) + cos(-pi)*cos(-11*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(1775*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (444),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-11) * pi / 12) * sin(-pi) + cos((-11) * pi / 12) * cos(-pi) = sin(-pi)*sin(-11*pi/12) + cos(-pi)*cos(-11*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(-11*pi/12) * sin(-pi) + cos(-11*pi/12) * cos(-pi),
{
have : cos(pi/12) = cos((-11*pi/12) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_619 : -sin(pi/7)*sin(76879*pi/84) - cos(pi/7)*cos(76879*pi/84)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(sin(76879 * pi / 84) * sin(pi / 7) + cos(76879 * pi / 84) * cos(pi / 7)) = -sin(pi/7)*sin(76879*pi/84) - cos(pi/7)*cos(76879*pi/84),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(10981*pi/12) = sin(76879*pi/84) * sin(pi/7) + cos(76879*pi/84) * cos(pi/7),
{
have : cos(10981*pi/12) = cos((76879*pi/84) - (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(10981*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (457),
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


lemma Trigo_number_generalization_step2_620 : sin(3010*pi/3)**2=1 - sin(-pi/6)**2:=
begin
have : (1 - 2 * sin(-pi / 6) ** 2) / 2 + 1 / 2 = 1 - sin(-pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : (-sin(3010 * pi / 3)) ** 2 = sin(3010*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(3010*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (501),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) ** 2 = cos(-pi/3) / 2 + 1 / 2,
{
have : cos(-pi/3) = cos(2*(-pi/6)),
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


lemma Trigo_number_generalization_step2_621 : -cos(pi/4)*cos(2811*pi/2) - sin(pi/4)*sin(2811*pi/2)=sqrt( 2 ) / 2:=
begin
have : -(sin(2811 * pi / 2) * sin(pi / 4) + cos(2811 * pi / 2) * cos(pi / 4)) = -cos(pi/4)*cos(2811*pi/2) - sin(pi/4)*sin(2811*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5621*pi/4) = sin(2811*pi/2) * sin(pi/4) + cos(2811*pi/2) * cos(pi/4),
{
have : cos(5621*pi/4) = cos((2811*pi/2) - (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(5621*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (702),
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


lemma Trigo_number_generalization_step2_622 : sin(9529*pi/6)*cos(pi) + sin(pi)*cos(9529*pi/6)=- 1 / 2:=
begin
have : sin(9535*pi/6) = sin(9529*pi/6) * cos(pi) + sin(pi) * cos(9529*pi/6),
{
have : sin(9535*pi/6) = sin((9529*pi/6) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(9535*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (794),
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


lemma Trigo_number_generalization_step2_623 : -sin(2679*pi/8)*cos(pi/8) - sin(pi/8)*cos(2679*pi/8)=sin(1702*pi):=
begin
have : -(sin(2679 * pi / 8) * cos(pi / 8) + sin(pi / 8) * cos(2679 * pi / 8)) = -sin(2679*pi/8)*cos(pi/8) - sin(pi/8)*cos(2679*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(335*pi) = sin(2679*pi/8) * cos(pi/8) + sin(pi/8) * cos(2679*pi/8),
{
have : sin(335*pi) = sin((2679*pi/8) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(335*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (168),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(1702*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (851),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_624 : -1 + 2*cos(-pi)**2=sin(4717*pi/2):=
begin
have : - -sin(4717 * pi / 2) = sin(4717*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(3063*pi/2) = -sin(4717*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3063*pi/2) (413),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * cos(-pi) ** 2 - 1 = -1 + 2*cos(-pi)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - sin(3063*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (764),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_625 (h0 : cos((622*pi)/2)≠ 0) (h1 : sin(622*pi)≠ 0) : (1 - cos(622*pi))/sin(622*pi)=1 / tan(1603*pi/2):=
begin
have : tan(311*pi) = ( 1 - cos(622*pi) ) / sin(622*pi),
{
have : tan(311*pi) = tan((622*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = tan(311*pi),
{
rw tan_eq_tan_add_int_mul_pi (2*pi) (309),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = 1 / tan(1603*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (803),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_626 : -1 + 2*(sin(-5*pi/24)*sin(-pi/8) + cos(-5*pi/24)*cos(-pi/8))**2=- cos(6979*pi/6):=
begin
have : -1 + 2 * (sin((-5) * pi / 24) * sin(-pi / 8) + cos((-5) * pi / 24) * cos(-pi / 8)) ** 2 = -1 + 2*(sin(-5*pi/24)*sin(-pi/8) + cos(-5*pi/24)*cos(-pi/8))**2,
{
field_simp at *,
},
have : cos(-pi/12) = sin(-5*pi/24) * sin(-pi/8) + cos(-5*pi/24) * cos(-pi/8),
{
have : cos(-pi/12) = cos((-5*pi/24) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(-pi / 12) ** 2 - 1 = -1 + 2*cos(-pi/12)**2,
{
field_simp at *,
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
have : cos(-pi/6) = - cos(6979*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (581),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_627 (h0 : cos(pi/6)≠ 0) (h1 : (1-tan(pi/6)**2)≠ 0) (h2 : cos(pi/12)≠ 0) (h3 : ((1-tan(pi/12)**2)*(-4*tan(pi/12)**2/(1-tan(pi/12)**2)**2+1))≠ 0) (h4 : (1-(2*tan(pi/12)/(1-tan(pi/12)**2))**2)≠ 0) (h5 : (1-tan(pi/12)**2)≠ 0) : 4*tan(pi/12)/((1 - tan(pi/12)**2)*(-4*tan(pi/12)**2/(1 - tan(pi/12)**2)**2 + 1))=sqrt( 3 ):=
begin
have : 2 * (2 * tan(pi / 12) / (1 - tan(pi / 12) ** 2)) / (1 - (2 * tan(pi / 12) / (1 - tan(pi / 12) ** 2)) ** 2) = 4*tan(pi/12)/((1 - tan(pi/12)**2)*(-4*tan(pi/12)**2/(1 - tan(pi/12)**2)**2 + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/3) = 2 * tan(pi/6) / ( 1 - tan(pi/6) ** 2 ),
{
have : tan(pi/3) = tan(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_628 (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) (h2 : (2*-sin(995*pi/2))≠ 0) (h3 : (2*sin(995*pi/2))≠ 0) : -sin(pi)/(2*sin(995*pi/2))=0:=
begin
have : sin(pi) / (2 * -sin(995 * pi / 2)) = -sin(pi)/(2*sin(995*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(995*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (249),
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
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_629 : -sin(-4*pi/45)*sin(pi/5) + cos(-4*pi/45)*cos(pi/5)=sin(52783*pi/18):=
begin
have : -sin((-4) * pi / 45) * sin(pi / 5) + cos((-4) * pi / 45) * cos(pi / 5) = -sin(-4*pi/45)*sin(pi/5) + cos(-4*pi/45)*cos(pi/5),
{
field_simp at *,
},
have : cos(pi/9) = -sin(-4*pi/45) * sin(pi/5) + cos(-4*pi/45) * cos(pi/5),
{
have : cos(pi/9) = cos((-4*pi/45) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(31219*pi/18) = sin(52783*pi/18),
{
rw sin_eq_sin_add_int_mul_two_pi (31219*pi/18) (599),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) = sin(31219*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (867),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_630 : cos(29*pi/42)*cos(16011*pi/14) + sin(29*pi/42)*cos(pi/7)=1 / 2:=
begin
have : cos(16011 * pi / 14) * cos(29 * pi / 42) + sin(29 * pi / 42) * cos(pi / 7) = cos(29*pi/42)*cos(16011*pi/14) + sin(29*pi/42)*cos(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = cos(16011*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (571),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(29 * pi / 42) * cos(pi / 7) + sin(pi / 7) * cos(29 * pi / 42) = sin(pi/7)*cos(29*pi/42) + sin(29*pi/42)*cos(pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(29*pi/42) * cos(pi/7) + sin(pi/7) * cos(29*pi/42),
{
have : sin(5*pi/6) = sin((29*pi/42) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_631 : (sin(-6*pi/5)*cos(pi) + sin(pi)*cos(-6*pi/5))*sin(-pi)=cos(-9*pi/5)*cos(pi)/2 - sin(-9*pi/5)*sin(pi)/2 - cos(-6*pi/5)/2:=
begin
have : sin(-pi) * (sin((-6) * pi / 5) * cos(pi) + sin(pi) * cos((-6) * pi / 5)) = (sin(-6*pi/5)*cos(pi) + sin(pi)*cos(-6*pi/5))*sin(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = sin(-6*pi/5) * cos(pi) + sin(pi) * cos(-6*pi/5),
{
have : sin(-pi/5) = sin((-6*pi/5) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin((-9) * pi / 5) * sin(pi) + cos((-9) * pi / 5) * cos(pi)) / 2 - cos((-6) * pi / 5) / 2 = cos(-9*pi/5)*cos(pi)/2 - sin(-9*pi/5)*sin(pi)/2 - cos(-6*pi/5)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi/5) = -sin(-9*pi/5) * sin(pi) + cos(-9*pi/5) * cos(pi),
{
have : cos(-4*pi/5) = cos((-9*pi/5) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) * sin(-pi/5) = cos(-4*pi/5) / 2 - cos(-6*pi/5) / 2,
{
rw sin_mul_sin,
have : cos((-pi) + (-pi/5)) = cos(-6*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-pi/5)) = cos(-4*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_632 : -cos(2297*pi/18)=-cos(6091*pi/18):=
begin
have : sin(8704*pi/9) = -cos(6091*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8704*pi/9) (652),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = -cos(2297*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(8704*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/9) (483),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_633 : -sin(pi/2)**2 + cos(pi/2)**2 + cos(2963*pi/3)=2 * cos(2*pi/3) * cos(pi/3):=
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
have : cos(-pi/3) = cos(2963*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (494),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step2_634 : -cos(pi/7)*cos(37671*pi/28) + sin(pi/7)*sin(11*pi/28)=sqrt( 2 ) / 2:=
begin
have : cos(pi / 7) * -cos(37671 * pi / 28) + sin(pi / 7) * sin(11 * pi / 28) = -cos(pi/7)*cos(37671*pi/28) + sin(pi/7)*sin(11*pi/28),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/28) = -cos(37671*pi/28),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (11*pi/28) (672),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11 * pi / 28) * sin(pi / 7) + cos(11 * pi / 28) * cos(pi / 7) = cos(pi/7)*cos(11*pi/28) + sin(pi/7)*sin(11*pi/28),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(11*pi/28) * sin(pi/7) + cos(11*pi/28) * cos(pi/7),
{
have : cos(pi/4) = cos((11*pi/28) - (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_635 : -sin(4665*pi/4)=sin(9047*pi/4):=
begin
have : - -sin(9047 * pi / 4) = sin(9047*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(5473*pi/4) = -sin(9047*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5473*pi/4) (446),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) = -sin(4665*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (583),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = - cos(5473*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/4) (684),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_636 (h0 : (sin((-6)*pi/5)*sin(-pi/5)+cos((-6)*pi/5)*cos(-pi/5))≠ 0) (h1 : (cos(-6*pi/5)*cos(-pi/5)+sin(-6*pi/5)*sin(-pi/5))≠ 0) (h2 : (cos((-6)*pi/5)*cos(-pi/5)+sin((-6)*pi/5)*-cos(10443*pi/10))≠ 0) (h3 : (cos(-6*pi/5)*cos(-pi/5)-sin(-6*pi/5)*cos(10443*pi/10))≠ 0) : tan(-pi)=sin(-pi)/(cos(-6*pi/5)*cos(-pi/5) - sin(-6*pi/5)*cos(10443*pi/10)):=
begin
have : sin(-pi) / (cos((-6) * pi / 5) * cos(-pi / 5) + sin((-6) * pi / 5) * -cos(10443 * pi / 10)) = sin(-pi)/(cos(-6*pi/5)*cos(-pi/5) - sin(-6*pi/5)*cos(10443*pi/10)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/5) = -cos(10443*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/5) (522),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) / (sin((-6) * pi / 5) * sin(-pi / 5) + cos((-6) * pi / 5) * cos(-pi / 5)) = sin(-pi)/(cos(-6*pi/5)*cos(-pi/5) + sin(-6*pi/5)*sin(-pi/5)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(-6*pi/5) * sin(-pi/5) + cos(-6*pi/5) * cos(-pi/5),
{
have : cos(-pi) = cos((-6*pi/5) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi) = sin(-pi) / cos(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_637 : cos(1447*pi)=- 1:=
begin
have : sin(1047*pi/2) = cos(1447*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1047*pi/2) (461),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(1047*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (261),
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


lemma Trigo_number_generalization_step2_638 : cos(-446*pi)=cos(684*pi):=
begin
have : - -cos((-446) * pi) = cos(-446*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(763*pi) = -cos(-446*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (763*pi) (158),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(763*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (380),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(684*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (341),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_639 : -cos(838*pi/3)=1 - 2*(sin(-pi/3)*cos(pi/6) + sin(pi/6)*cos(-pi/3))**2:=
begin
have : cos(-pi/3) = -cos(838*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (139),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(-pi/3) * cos(pi/6) + sin(pi/6) * cos(-pi/3),
{
have : sin(-pi/6) = sin((-pi/3) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_640 : -sin(271*pi)=0:=
begin
have : cos(477*pi/2) = -sin(271*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (477*pi/2) (254),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(477*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (119),
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


lemma Trigo_number_generalization_step2_641 : -2*cos(-pi)*cos(pi/8)*cos(10229*pi/8)=sin(5*pi/4) / 2 + sin(-3*pi/4) / 2:=
begin
have : 2 * -cos(10229 * pi / 8) * cos(-pi) * cos(pi / 8) = -2*cos(-pi)*cos(pi/8)*cos(10229*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -cos(10229*pi/8),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/8) (639),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 8) * cos(pi / 8) + sin(pi / 8) * cos(pi / 8)) * cos(-pi) = 2*sin(pi/8)*cos(-pi)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(pi/8) * cos(pi/8) + sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin((pi/8) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) * cos(-pi) = sin(5*pi/4) / 2 + sin(-3*pi/4) / 2,
{
rw sin_mul_cos,
have : sin((pi/4) + (-pi)) = sin(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/4) - (-pi)) = sin(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_642 : -cos(1321*pi/12)=(1 - 2*sin(pi/8)**2)*sin(-pi/3) - sin(pi/4)*cos(-pi/3):=
begin
have : sin(-7*pi/12) = -cos(1321*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-7*pi/12) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 3) * (1 - 2 * sin(pi / 8) ** 2) - sin(pi / 4) * cos(-pi / 3) = (1 - 2*sin(pi/8)**2)*sin(-pi/3) - sin(pi/4)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = 1 - 2 * sin(pi/8) ** 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-7*pi/12) = sin(-pi/3) * cos(pi/4) - sin(pi/4) * cos(-pi/3),
{
have : sin(-7*pi/12) = sin((-pi/3) - (pi/4)),
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


lemma Trigo_number_generalization_step2_643 : cos(2246*pi)=1:=
begin
have : - -cos(2246 * pi) = cos(2246*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1691*pi/2) = -cos(2246*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1691*pi/2) (700),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(1691*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (423),
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


lemma Trigo_number_generalization_step2_644 (h0 : tan(4083*pi/10)≠ 0) (h1 : cos(4083*pi/20)≠ 0) (h2 : (1-tan(4083*pi/20)**2)≠ 0) (h3 : (2*tan(4083*pi/20))≠ 0) (h4 : (2*tan(4083*pi/20)/(1-tan(4083*pi/20)**2))≠ 0) : (1 - tan(4083*pi/20)**2)/(2*tan(4083*pi/20))=- tan(1734*pi/5):=
begin
have : 1 / (2 * tan(4083 * pi / 20) / (1 - tan(4083 * pi / 20) ** 2)) = (1 - tan(4083*pi/20)**2)/(2*tan(4083*pi/20)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(4083*pi/10) = 2 * tan(4083*pi/20) / ( 1 - tan(4083*pi/20) ** 2 ),
{
have : tan(4083*pi/10) = tan(2*(4083*pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/5) = 1 / tan(4083*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/5) (408),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/5) = - tan(1734*pi/5),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/5) (347),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_645 : sin(5645*pi/3)**2=1 - sin(6215*pi/6)**2:=
begin
have : 1 - (-sin(6215 * pi / 6)) ** 2 = 1 - sin(6215*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -sin(6215*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (517),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-sin(5645 * pi / 3)) ** 2 = sin(5645*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(5645*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (941),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 = 1 - cos(pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_646 (h0 : cos(463*pi)≠ 0) : sin(463*pi)/cos(463*pi)=- tan(40*pi):=
begin
have : tan(463*pi) = sin(463*pi) / cos(463*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = tan(463*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (465),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = - tan(40*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_647 (h0 : cos(3803*pi/4)≠ 0) (h1 : (2*cos(3803*pi/4))≠ 0) : sin(3803*pi/2)/(2*cos(3803*pi/4))=sqrt( 2 ) / 2:=
begin
have : sin(3803*pi/4) = sin(3803*pi/2) / ( 2 * cos(3803*pi/4) ),
{
have : sin(3803*pi/2) = sin(2*(3803*pi/4)),
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
have : cos(pi/4) = sin(3803*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/4) (475),
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


lemma Trigo_number_generalization_step2_648 (h0 : cos(-2*pi)≠ 0) (h1 : (2*sin(1409*pi/2))≠ 0) : sin(-13*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(-13*pi/6)=sin(-4*pi)/(2*sin(1409*pi/2)):=
begin
have : sin((-13) * pi / 6) * cos(-pi / 6) - sin(-pi / 6) * cos((-13) * pi / 6) = sin(-13*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(-13*pi/6),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-13*pi/6) * cos(-pi/6) - sin(-pi/6) * cos(-13*pi/6),
{
have : sin(-2*pi) = sin((-13*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-4) * pi) / (2 * sin(1409 * pi / 2)) = sin(-4*pi)/(2*sin(1409*pi/2)),
{
field_simp at *,
},
have : cos(-2*pi) = sin(1409*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (351),
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


lemma Trigo_number_generalization_step2_649 : sin(803*pi/4)=2*sin(pi/8)*cos(7409*pi/8):=
begin
have : cos(pi/8) = cos(7409*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/8) (463),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) = sin(803*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = 2 * sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_650 : sin(-pi/6)*sin(pi/2) - sin(5777*pi/3)*cos(pi/2)=- 1 / 2:=
begin
have : sin(-pi / 6) * sin(pi / 2) + -sin(5777 * pi / 3) * cos(pi / 2) = sin(-pi/6)*sin(pi/2) - sin(5777*pi/3)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(5777*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (962),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 2) * sin(-pi / 6) + cos(pi / 2) * cos(-pi / 6) = sin(-pi/6)*sin(pi/2) + cos(-pi/6)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(pi/2) * sin(-pi/6) + cos(pi/2) * cos(-pi/6),
{
have : cos(2*pi/3) = cos((pi/2) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_651 : 3*cos(3149*pi/18) - 4*cos(3149*pi/18)**3=sqrt( 3 ) / 2:=
begin
have : -(4 * cos(3149 * pi / 18) ** 3 - 3 * cos(3149 * pi / 18)) = 3*cos(3149*pi/18) - 4*cos(3149*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3149*pi/6) = 4 * cos(3149*pi/18) ** 3 - 3 * cos(3149*pi/18),
{
have : cos(3149*pi/6) = cos(3*(3149*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(3149*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (262),
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


lemma Trigo_number_generalization_step2_652 (h0 : tan(7235*pi/6)≠ 0) : -1/tan(7235*pi/6)=sqrt( 3 ):=
begin
have : (-1) / tan(7235 * pi / 6) = -1/tan(7235*pi/6),
{
field_simp at *,
},
have : tan(925*pi/3) = -1 / tan(7235*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (925*pi/3) (897),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(925*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (308),
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


lemma Trigo_number_generalization_step2_653 (h0 : sin(-pi/4)≠ 0) (h1 : (2*sin(-pi/4))≠ 0) : sin(-pi/2)*cos(-3*pi/8)/(2*sin(-pi/4)) + sin(-3*pi/8)*sin(-pi/4)=cos(5457*pi/8):=
begin
have : cos((-3) * pi / 8) * (sin(-pi / 2) / (2 * sin(-pi / 4))) + sin((-3) * pi / 8) * sin(-pi / 4) = sin(-pi/2)*cos(-3*pi/8)/(2*sin(-pi/4)) + sin(-3*pi/8)*sin(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(-pi/2) / ( 2 * sin(-pi/4) ),
{
have : sin(-pi/2) = sin(2*(-pi/4)),
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
have : sin((-3) * pi / 8) * sin(-pi / 4) + cos((-3) * pi / 8) * cos(-pi / 4) = cos(-3*pi/8)*cos(-pi/4) + sin(-3*pi/8)*sin(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = sin(-3*pi/8) * sin(-pi/4) + cos(-3*pi/8) * cos(-pi/4),
{
have : cos(-pi/8) = cos((-3*pi/8) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = cos(5457*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/8) (341),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_654 : -1 + 2*sin(27541*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -1 + 2 * (-sin(27541 * pi / 24)) ** 2 = -1 + 2*sin(27541*pi/24)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -sin(27541*pi/24),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/24) (573),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 24) ** 2 - 1 = -1 + 2*cos(pi/24)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = 2 * cos(pi/24) ** 2 - 1,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_655 : -sin(-pi)*sin(4*pi/3) + cos(-pi)*cos(4774*pi/3)=1 / 2:=
begin
have : cos(4*pi/3) = cos(4774*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (4*pi/3) (795),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_656 : 1 - 2*sin(5615*pi/8)**2=sqrt( 2 ) / 2:=
begin
have : cos(5615*pi/4) = 1 - 2 * sin(5615*pi/8) ** 2,
{
have : cos(5615*pi/4) = cos(2*(5615*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = cos(5615*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/4) (702),
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


lemma Trigo_number_generalization_step2_657 : -sin(-pi)*sin(5*pi/4) + sin(575*pi/2)*cos(5*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(-pi) = sin(575*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (143),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 4) * sin(-pi) + cos(5 * pi / 4) * cos(-pi) = -sin(-pi)*sin(5*pi/4) + cos(-pi)*cos(5*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(5*pi/4) * sin(-pi) + cos(5*pi/4) * cos(-pi),
{
have : cos(pi/4) = cos((5*pi/4) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_658 (h0 : cos(11069*pi/9)≠ 0) (h1 : tan(6851*pi/18)≠ 0) : sin(pi/9)/cos(11069*pi/9)=-1/tan(6851*pi/18):=
begin
have : (-1) / tan(6851 * pi / 18) = -1/tan(6851*pi/18),
{
field_simp at *,
},
have : tan(pi/9) = -1 / tan(6851*pi/18),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/9) (380),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) = cos(11069*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (615),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) / cos(pi/9) = tan(pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_659 (h0 : cos((pi/3)/2)≠ 0) (h1 : (cos(pi/3)+1)≠ 0) (h2 : (1+cos(pi/3))≠ 0) (h3 : (-sin(4*pi/21)*sin(pi/7)+cos(4*pi/21)*cos(pi/7)+1)≠ 0) (h4 : (-sin(pi/7)*sin(4*pi/21)+cos(pi/7)*cos(4*pi/21)+1)≠ 0) : sin(pi/3)/(-sin(pi/7)*sin(4*pi/21) + cos(pi/7)*cos(4*pi/21) + 1)=sqrt( 3 ) / 3:=
begin
have : sin(pi / 3) / (-sin(4 * pi / 21) * sin(pi / 7) + cos(4 * pi / 21) * cos(pi / 7) + 1) = sin(pi/3)/(-sin(pi/7)*sin(4*pi/21) + cos(pi/7)*cos(4*pi/21) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(4*pi/21) * sin(pi/7) + cos(4*pi/21) * cos(pi/7),
{
have : cos(pi/3) = cos((4*pi/21) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_660 : -1 + 2*cos(3*pi/16)**2=sin(pi/8)*sin(7567*pi/4) + cos(pi/8)*cos(pi/4):=
begin
have : 2 * cos(3 * pi / 16) ** 2 - 1 = -1 + 2*cos(3*pi/16)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = 2 * cos(3*pi/16) ** 2 - 1,
{
have : cos(3*pi/8) = cos(2*(3*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 8) * -sin(7567 * pi / 4) + cos(pi / 8) * cos(pi / 4) = sin(pi/8)*sin(7567*pi/4) + cos(pi/8)*cos(pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) = -sin(7567*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/4) (946),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/8) = - sin(pi/8) * sin(pi/4) + cos(pi/8) * cos(pi/4),
{
have : cos(3*pi/8) = cos((pi/8) + (pi/4)),
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


lemma Trigo_number_generalization_step2_661 (h0 : tan(14929*pi/18)≠ 0) (h1 : cos(14929*pi/36)≠ 0) (h2 : (2*tan(14929*pi/36)/(1-tan(14929*pi/36)**2))≠ 0) (h3 : (2*tan(14929*pi/36))≠ 0) (h4 : (1-tan(14929*pi/36)**2)≠ 0) : (1 - tan(14929*pi/36)**2)/(2*tan(14929*pi/36))=tan(6985*pi/9):=
begin
have : 1 / (2 * tan(14929 * pi / 36) / (1 - tan(14929 * pi / 36) ** 2)) = (1 - tan(14929*pi/36)**2)/(2*tan(14929*pi/36)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(14929*pi/18) = 2 * tan(14929*pi/36) / ( 1 - tan(14929*pi/36) ** 2 ),
{
have : tan(14929*pi/18) = tan(2*(14929*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 1 / tan(14929*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/9) (829),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = tan(6985*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (776),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_662 : -cos(5794*pi/3)=cos(4901*pi/3):=
begin
have : - -cos(4901 * pi / 3) = cos(4901*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1487*pi/6) = -cos(4901*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1487*pi/6) (940),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -cos(5794*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (965),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(1487*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (124),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_663 (h0 : cos((542*pi)/2)≠ 0) (h1 : sin(542*pi)≠ 0) : (1 - cos(542*pi))/sin(542*pi)=0:=
begin
have : tan(271*pi) = ( 1 - cos(542*pi) ) / sin(542*pi),
{
have : tan(271*pi) = tan((542*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = tan(271*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (270),
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


lemma Trigo_number_generalization_step2_664 : (cos(-pi/9)*cos(4*pi/9) - (-4*sin(4*pi/27)**3 + 3*sin(4*pi/27))*sin(-pi/9))*cos(pi/2)=cos(pi/6) / 2 + cos(5*pi/6) / 2:=
begin
have : (cos(-pi / 9) * cos(4 * pi / 9) - sin(-pi / 9) * ((-4) * sin(4 * pi / 27) ** 3 + 3 * sin(4 * pi / 27))) * cos(pi / 2) = (cos(-pi/9)*cos(4*pi/9) - (-4*sin(4*pi/27)**3 + 3*sin(4*pi/27))*sin(-pi/9))*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = -4 * sin(4*pi/27) ** 3 + 3 * sin(4*pi/27),
{
have : sin(4*pi/9) = sin(3*(4*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 2) * (-sin(4 * pi / 9) * sin(-pi / 9) + cos(4 * pi / 9) * cos(-pi / 9)) = (cos(-pi/9)*cos(4*pi/9) - sin(-pi/9)*sin(4*pi/9))*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(4*pi/9) * sin(-pi/9) + cos(4*pi/9) * cos(-pi/9),
{
have : cos(pi/3) = cos((4*pi/9) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
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


lemma Trigo_number_generalization_step2_665 : -cos(-11821*pi/10)=- 4 * sin(-pi/5) ** 3 + 3 * sin(-pi/5):=
begin
have : -cos((-11821) * pi / 10) = -cos(-11821*pi/10),
{
field_simp at *,
},
have : sin(8173*pi/5) = cos(-11821*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (8173*pi/5) (226),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/5) = -sin(8173*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-3*pi/5) (817),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/5) = - 4 * sin(-pi/5) ** 3 + 3 * sin(-pi/5),
{
have : sin(-3*pi/5) = sin(3*(-pi/5)),
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


lemma Trigo_number_generalization_step2_666 : -(3*sin(4397*pi/8) - 4*sin(4397*pi/8)**3)*cos(-pi/2)=sin(3*pi/8) / 2 + sin(-5*pi/8) / 2:=
begin
have : -((-4) * sin(4397 * pi / 8) ** 3 + 3 * sin(4397 * pi / 8)) * cos(-pi / 2) = -(3*sin(4397*pi/8) - 4*sin(4397*pi/8)**3)*cos(-pi/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13191*pi/8) = -4 * sin(4397*pi/8) ** 3 + 3 * sin(4397*pi/8),
{
have : sin(13191*pi/8) = sin(3*(4397*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -sin(13191*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/8) (824),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) * cos(-pi/2) = sin(3*pi/8) / 2 + sin(-5*pi/8) / 2,
{
rw sin_mul_cos,
have : sin((-pi/8) + (-pi/2)) = sin(-5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/8) - (-pi/2)) = sin(3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_667 : sin(1536*pi)**2=1 / 2 - cos(-2*pi) / 2:=
begin
have : (-sin(1536 * pi)) ** 2 = sin(1536*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(589*pi) = -sin(1536*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (589*pi) (473),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(589*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (295),
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


lemma Trigo_number_generalization_step2_668 : sin(pi/9)*sin(40847*pi/36) - cos(pi/9)*cos(40847*pi/36)=sqrt( 2 ) / 2:=
begin
have : -(-sin(40847 * pi / 36) * sin(pi / 9) + cos(40847 * pi / 36) * cos(pi / 9)) = sin(pi/9)*sin(40847*pi/36) - cos(pi/9)*cos(40847*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4539*pi/4) = -sin(40847*pi/36) * sin(pi/9) + cos(40847*pi/36) * cos(pi/9),
{
have : cos(4539*pi/4) = cos((40847*pi/36) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(4539*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/4) (567),
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


lemma Trigo_number_generalization_step2_669 : 4*sin(24187*pi/18)**3 - 3*sin(24187*pi/18)=1 / 2:=
begin
have : (-4) * (-sin(24187 * pi / 18)) ** 3 + 3 * -sin(24187 * pi / 18) = 4*sin(24187*pi/18)**3 - 3*sin(24187*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = -sin(24187*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/18) (672),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(5 * pi / 18) ** 3 + 3 * sin(5 * pi / 18) = -4*sin(5*pi/18)**3 + 3*sin(5*pi/18),
{
field_simp at *,
},
have : sin(5*pi/6) = -4 * sin(5*pi/18) ** 3 + 3 * sin(5*pi/18),
{
have : sin(5*pi/6) = sin(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_670 : cos(6964*pi/5)*cos(1471*pi)=cos(-9*pi/5) / 2 + cos(11*pi/5) / 2:=
begin
have : - -cos(1471 * pi) * cos(6964 * pi / 5) = cos(6964*pi/5)*cos(1471*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -cos(1471*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (736),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(6964 * pi / 5) * cos(2 * pi) = -cos(2*pi)*cos(6964*pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -cos(6964*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/5) (696),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) * cos(2*pi) = cos(-9*pi/5) / 2 + cos(11*pi/5) / 2,
{
rw cos_mul_cos,
have : cos((pi/5) + (2*pi)) = cos(11*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/5) - (2*pi)) = cos(-9*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_671 (h0 : tan(2018*pi/3)≠ 0) (h1 : (1/tan((-283)*pi/6))≠ 0) (h2 : tan((-283)*pi/6)≠ 0) : tan(-283*pi/6)=tan(5669*pi/6):=
begin
have : 1 / (1 / tan((-283) * pi / 6)) = tan(-283*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2018*pi/3) = 1 / tan(-283*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2018*pi/3) (625),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = 1 / tan(2018*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (672),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = tan(5669*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (945),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_672 : -3*sin(6745*pi/18) + 4*sin(6745*pi/18)**3=- sin(6641*pi/6):=
begin
have : -((-4) * sin(6745 * pi / 18) ** 3 + 3 * sin(6745 * pi / 18)) = -3*sin(6745*pi/18) + 4*sin(6745*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(6745*pi/6) = -4 * sin(6745*pi/18) ** 3 + 3 * sin(6745*pi/18),
{
have : sin(6745*pi/6) = sin(3*(6745*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(6745*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (562),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(6641*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (553),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_673 (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) (h2 : (sin(11*pi/6)*cos(-pi/6)-sin(-pi/6)*cos(11*pi/6))≠ 0) : (1 - cos(2*pi))/(sin(11*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(11*pi/6))=0:=
begin
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
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_674 : cos(5516*pi/5)**2=1 - cos(4627*pi/10)**2:=
begin
have : (-cos(5516 * pi / 5)) ** 2 = cos(5516*pi/5)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = -cos(5516*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/5) (551),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = cos(4627*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/5) (231),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) ** 2 = 1 - sin(-pi/5) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_675 : -cos(25913*pi/36)**2 + sin(25913*pi/36)**2=- sin(4382*pi/9):=
begin
have : -(-sin(25913 * pi / 36) ** 2 + cos(25913 * pi / 36) ** 2) = -cos(25913*pi/36)**2 + sin(25913*pi/36)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(25913*pi/18) = -sin(25913*pi/36) ** 2 + cos(25913*pi/36) ** 2,
{
have : cos(25913*pi/18) = cos(2*(25913*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = -cos(25913*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (719),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = - sin(4382*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (243),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_676 (h0 : cos((4*pi/3)/2)≠ 0) (h1 : (1+cos(4*pi/3))≠ 0) (h2 : (cos(4*pi/3)+1)≠ 0) : -cos(2305*pi/6)/(cos(4*pi/3) + 1)=- sqrt( 3 ):=
begin
have : sin(4*pi/3) = -cos(2305*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/3) (192),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 3) / (1 + cos(4 * pi / 3)) = sin(4*pi/3)/(cos(4*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = sin(4*pi/3) / ( 1 + cos(4*pi/3) ),
{
have : tan(2*pi/3) = tan((4*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_677 (h0 : cos((2*pi/9)/2)≠ 0) (h1 : sin(2*pi/9)≠ 0) (h2 : cos((8989*pi/9)/2)≠ 0) (h3 : ((1-cos(8989*pi/9))/sin(8989*pi/9))≠ 0) (h4 : (1-cos(8989*pi/9))≠ 0) (h5 : sin(8989*pi/9)≠ 0) : (1 - cos(2*pi/9))/sin(2*pi/9)=sin(8989*pi/9)/(1 - cos(8989*pi/9)):=
begin
have : 1 / ((1 - cos(8989 * pi / 9)) / sin(8989 * pi / 9)) = sin(8989*pi/9)/(1 - cos(8989*pi/9)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(8989*pi/18) = ( 1 - cos(8989*pi/9) ) / sin(8989*pi/9),
{
have : tan(8989*pi/18) = tan((8989*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : tan(pi/9) = ( 1 - cos(2*pi/9) ) / sin(2*pi/9),
{
have : tan(pi/9) = tan((2*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 1 / tan(8989*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/9) (499),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_678 : sin(17429*pi/10)=2 * cos(-pi/5) ** 2 - 1:=
begin
have : - -sin(17429 * pi / 10) = sin(17429*pi/10),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3567*pi/5) = -sin(17429*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3567*pi/5) (514),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = -cos(3567*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi/5) (356),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = 2 * cos(-pi/5) ** 2 - 1,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_679 : 3*sin(7193*pi/12) - 4*sin(7193*pi/12)**3=sqrt( 2 ) / 2:=
begin
have : (-4) * sin(7193 * pi / 12) ** 3 + 3 * sin(7193 * pi / 12) = 3*sin(7193*pi/12) - 4*sin(7193*pi/12)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7193*pi/4) = -4 * sin(7193*pi/12) ** 3 + 3 * sin(7193*pi/12),
{
have : sin(7193*pi/4) = sin(3*(7193*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(7193*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (899),
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


lemma Trigo_number_generalization_step2_680 : cos(-2*pi/3)=1 - 2*(3*sin(-pi/9) - 4*sin(-pi/9)**3)**2:=
begin
have : 1 - 2 * ((-4) * sin(-pi / 9) ** 3 + 3 * sin(-pi / 9)) ** 2 = 1 - 2*(3*sin(-pi/9) - 4*sin(-pi/9)**3)**2,
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
have : -sin(-pi / 3) ** 2 + (1 - sin(-pi / 3) ** 2) = 1 - 2*sin(-pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) ** 2 = 1 - sin(-pi/3) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) = - sin(-pi/3) ** 2 + cos(-pi/3) ** 2,
{
have : cos(-2*pi/3) = cos(2*(-pi/3)),
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


lemma Trigo_number_generalization_step2_681 : cos(-3533*pi/4)=- 4 * sin(-pi/4) ** 3 + 3 * sin(-pi/4):=
begin
have : cos((-3533) * pi / 4) = cos(-3533*pi/4),
{
field_simp at *,
},
have : cos(5925*pi/4) = cos(-3533*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5925*pi/4) (299),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/4) = cos(5925*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-3*pi/4) (740),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/4) = - 4 * sin(-pi/4) ** 3 + 3 * sin(-pi/4),
{
have : sin(-3*pi/4) = sin(3*(-pi/4)),
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


lemma Trigo_number_generalization_step2_682 : -cos(pi/2)/2 + 1/2 + sin(6293*pi/4)**2=1:=
begin
have : 1 / 2 - cos(pi / 2) / 2 + sin(6293 * pi / 4) ** 2 = -cos(pi/2)/2 + 1/2 + sin(6293*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) ** 2 = 1 / 2 - cos(pi/2) / 2,
{
have : cos(pi/2) = cos(2*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 4) ** 2 + (-sin(6293 * pi / 4)) ** 2 = sin(pi/4)**2 + sin(6293*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(6293*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (786),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) ** 2 + cos(pi/4) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_683 : cos(34859*pi/30)=sin(3351*pi/5)*cos(pi/3) + sin(pi/3)*cos(pi/5):=
begin
have : sin(pi/5) = sin(3351*pi/5),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/5) (335),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(8*pi/15) = cos(34859*pi/30),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (8*pi/15) (581),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8*pi/15) = sin(pi/5) * cos(pi/3) + sin(pi/3) * cos(pi/5),
{
have : sin(8*pi/15) = sin((pi/5) + (pi/3)),
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


lemma Trigo_number_generalization_step2_684 : cos(8149*pi/6)=2*sin(2524*pi/3)*cos(2524*pi/3):=
begin
have : sin(5048*pi/3) = 2 * sin(2524*pi/3) * cos(2524*pi/3),
{
have : sin(5048*pi/3) = sin(2*(2524*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = cos(8149*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (679),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(5048*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (841),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_685 : 1 - 2*sin(3*pi/4)**2=-sin(-pi/2)*cos(2463*pi/2) + cos(-pi/2)*cos(pi):=
begin
have : cos(3*pi/2) = 1 - 2 * sin(3*pi/4) ** 2,
{
have : cos(3*pi/2) = cos(2*(3*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : -cos(2463 * pi / 2) * sin(-pi / 2) + cos(pi) * cos(-pi / 2) = -sin(-pi/2)*cos(2463*pi/2) + cos(-pi/2)*cos(pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -cos(2463*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (615),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/2) = sin(pi) * sin(-pi/2) + cos(pi) * cos(-pi/2),
{
have : cos(3*pi/2) = cos((pi) - (-pi/2)),
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


lemma Trigo_number_generalization_step2_686 : sin(-pi/5)*sin(1936*pi/5) - cos(-pi/5)*cos(1936*pi/5)=1:=
begin
have : -(-sin(1936 * pi / 5) * sin(-pi / 5) + cos(1936 * pi / 5) * cos(-pi / 5)) = sin(-pi/5)*sin(1936*pi/5) - cos(-pi/5)*cos(1936*pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(387*pi) = -sin(1936*pi/5) * sin(-pi/5) + cos(1936*pi/5) * cos(-pi/5),
{
have : cos(387*pi) = cos((1936*pi/5) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(387*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (193),
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


lemma Trigo_number_generalization_step2_687 : 2*(1 - 2*sin(-pi/12)**2)*sin(-pi/6)=cos(5813*pi/6):=
begin
have : 2 * sin(-pi / 6) * (1 - 2 * sin(-pi / 12) ** 2) = 2*(1 - 2*sin(-pi/12)**2)*sin(-pi/6),
{
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
have : sin(-pi/3) = cos(5813*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (484),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_688 : sin(pi/7)*cos(1882*pi/7) + sin(1882*pi/7)*cos(pi/7)=0:=
begin
have : sin(1882 * pi / 7) * cos(pi / 7) + sin(pi / 7) * cos(1882 * pi / 7) = sin(pi/7)*cos(1882*pi/7) + sin(1882*pi/7)*cos(pi/7),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(269*pi) = sin(1882*pi/7) * cos(pi/7) + sin(pi/7) * cos(1882*pi/7),
{
have : sin(269*pi) = sin((1882*pi/7) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(269*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (134),
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


lemma Trigo_number_generalization_step2_689 (h0 : cos(-4*pi/45)≠ 0) (h1 : cos(pi/9)≠ 0) (h2 : (tan(-4*pi/45)*tan(pi/9)+1)≠ 0) (h3 : (1+tan((-4)*pi/45)*tan(pi/9))≠ 0) (h4 : cos(-4*pi/45)≠ 0) (h5 : cos(pi/9)≠ 0) (h6 : 1 + tan(-4*pi/45) * tan(pi/9)≠ 0) (h7 : (tan((-4)*pi/45)*tan(pi/9)+1)≠ 0) : tan(-pi/5)=1 / tan(2887*pi/10):=
begin
have : (tan((-4) * pi / 45) * tan(pi / 9) + 1) * tan(-pi / 5) / (tan((-4) * pi / 45) * tan(pi / 9) + 1) = tan(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-4*pi/45) - tan(pi/9) = ( tan(-4*pi/45) * tan(pi/9) + 1 ) * tan(-pi/5),
{
rw tan_sub_tan,
have : tan((-4*pi/45) - (pi/9)) = tan(-pi/5),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-4*pi/45) - tan(pi/9)) = (-tan(pi/9)+tan(-4*pi/45)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan((-4) * pi / 45) - tan(pi / 9)) / (1 + tan((-4) * pi / 45) * tan(pi / 9)) = (-tan(pi/9) + tan(-4*pi/45))/(tan(-4*pi/45)*tan(pi/9) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = ( tan(-4*pi/45) - tan(pi/9) ) / ( 1 + tan(-4*pi/45) * tan(pi/9) ),
{
have : tan(-pi/5) = tan((-4*pi/45) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = 1 / tan(2887*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/5) (288),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_690 : 1 - 2*sin(1111*pi)**2=sin(345*pi/2):=
begin
have : 1 - 2 * (-sin(1111 * pi)) ** 2 = 1 - 2*sin(1111*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(1111*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (556),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = 1 - 2 * sin(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(345*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_691 (h0 : cos(-7*pi/4)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (1+tan((-7)*pi/4)*tan((-2)*pi))≠ 0) (h3 : (tan(-2*pi)*tan(-7*pi/4)+1)≠ 0) (h4 : (-tan(-2*pi)*tan(2627*pi/4)+1)≠ 0) (h5 : (tan((-2)*pi)*-tan(2627*pi/4)+1)≠ 0) : (-tan(-2*pi) - tan(2627*pi/4))/(-tan(-2*pi)*tan(2627*pi/4) + 1)=1:=
begin
have : (-tan((-2) * pi) + -tan(2627 * pi / 4)) / (tan((-2) * pi) * -tan(2627 * pi / 4) + 1) = (-tan(-2*pi) - tan(2627*pi/4))/(-tan(-2*pi)*tan(2627*pi/4) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-7*pi/4) = -tan(2627*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-7*pi/4) (655),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_692 (h0 : cos(964*pi/9)≠ 0) (h1 : (2*cos(964*pi/9))≠ 0) : cos(3647*pi/18)=sin(1928*pi/9)/(2*cos(964*pi/9)):=
begin
have : sin(964*pi/9) = sin(1928*pi/9) / ( 2 * cos(964*pi/9) ),
{
have : sin(1928*pi/9) = sin(2*(964*pi/9)),
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
have : sin(-pi/9) = cos(3647*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/9) (101),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(964*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/9) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_693 : sin(-2*pi) ** 2=1 - (cos(8*pi/3)/2 + cos(-2*pi)/2 - sin(-7*pi/3)*sin(pi/3))**2:=
begin
have : 1 - (cos(8 * pi / 3) / 2 + cos((-2) * pi) / 2 - sin((-7) * pi / 3) * sin(pi / 3)) ** 2 = 1 - (cos(8*pi/3)/2 + cos(-2*pi)/2 - sin(-7*pi/3)*sin(pi/3))**2,
{
field_simp at *,
},
have : cos(pi/3) * cos(-7*pi/3) = cos(8*pi/3) / 2 + cos(-2*pi) / 2,
{
rw cos_mul_cos,
have : cos((pi/3) + (-7*pi/3)) = cos(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (-7*pi/3)) = cos(8*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (cos(pi/3) * cos(-7*pi/3)) = cos(-7*pi/3)*cos(pi/3),
{
ring,
},
conv {to_rhs, rw this,},
have : 1 - (-sin((-7) * pi / 3) * sin(pi / 3) + cos((-7) * pi / 3) * cos(pi / 3)) ** 2 = 1 - (cos(-7*pi/3)*cos(pi/3) - sin(-7*pi/3)*sin(pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -sin(-7*pi/3) * sin(pi/3) + cos(-7*pi/3) * cos(pi/3),
{
have : cos(-2*pi) = cos((-7*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) ** 2 = 1 - cos(-2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_694 : -sin(4235*pi/2)=- sin(4003*pi/2):=
begin
have : cos(1951*pi) = sin(4235*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (1951*pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -cos(1951*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (974),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - sin(4003*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_695 : 1 - 2*sin(pi/6)**2=cos(6067*pi/3):=
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
have : - -cos(6067 * pi / 3) = cos(6067*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(11111*pi/6) = -cos(6067*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (11111*pi/6) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = - sin(11111*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (925),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_696 : -2*sin(pi/8)*sin(3051*pi/8)=sqrt( 2 ) / 2:=
begin
have : 2 * sin(pi / 8) * -sin(3051 * pi / 8) = -2*sin(pi/8)*sin(3051*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(3051*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (190),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = 2 * sin(pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_697 : -cos(1165*pi/4)=sin(1318*pi)*cos(pi/4) + sin(pi/4)*cos(1318*pi):=
begin
have : sin(5273*pi/4) = sin(1318*pi) * cos(pi/4) + sin(pi/4) * cos(1318*pi),
{
have : sin(5273*pi/4) = sin((1318*pi) + (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = -cos(1165*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (145),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(5273*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/4) (659),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_698 : cos(1063*pi)=- 1:=
begin
have : - -cos(1063 * pi) = cos(1063*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(326*pi) = -cos(1063*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (326*pi) (368),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(326*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (163),
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


lemma Trigo_number_generalization_step2_699 : -cos(14287*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(4655*pi/12) = cos(14287*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4655*pi/12) (789),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(4655*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (194),
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


lemma Trigo_number_generalization_step2_700 (h0 : cos(pi/5)≠ 0) (h1 : (2*cos(pi/5))≠ 0) : -sin(2*pi/5)*cos(7*pi/10)/(2*cos(pi/5)) + sin(7*pi/10)*cos(pi/5)=1:=
begin
have : -(sin(2 * pi / 5) / (2 * cos(pi / 5))) * cos(7 * pi / 10) + sin(7 * pi / 10) * cos(pi / 5) = -sin(2*pi/5)*cos(7*pi/10)/(2*cos(pi/5)) + sin(7*pi/10)*cos(pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = sin(2*pi/5) / ( 2 * cos(pi/5) ),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
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
have : sin(7 * pi / 10) * cos(pi / 5) - sin(pi / 5) * cos(7 * pi / 10) = -sin(pi/5)*cos(7*pi/10) + sin(7*pi/10)*cos(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(7*pi/10) * cos(pi/5) - sin(pi/5) * cos(7*pi/10),
{
have : sin(pi/2) = sin((7*pi/10) - (pi/5)),
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


lemma Trigo_number_generalization_step2_701 (h0 : cos(19*pi/20)≠ 0) (h1 : cos(pi/5)≠ 0) (h2 : (1+tan(19*pi/20)*tan(pi/5))≠ 0) (h3 : (tan(pi/5)*tan(19*pi/20)+1)≠ 0) (h4 : (-tan(pi/5)*tan(17761*pi/20)+1)≠ 0) (h5 : (tan(pi/5)*-tan(17761*pi/20)+1)≠ 0) : (-tan(pi/5) - tan(17761*pi/20))/(-tan(pi/5)*tan(17761*pi/20) + 1)=- 1:=
begin
have : (-tan(pi / 5) + -tan(17761 * pi / 20)) / (tan(pi / 5) * -tan(17761 * pi / 20) + 1) = (-tan(pi/5) - tan(17761*pi/20))/(-tan(pi/5)*tan(17761*pi/20) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(19*pi/20) = -tan(17761*pi/20),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (19*pi/20) (889),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(19 * pi / 20) - tan(pi / 5)) / (1 + tan(19 * pi / 20) * tan(pi / 5)) = (-tan(pi/5) + tan(19*pi/20))/(tan(pi/5)*tan(19*pi/20) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = ( tan(19*pi/20) - tan(pi/5) ) / ( 1 + tan(19*pi/20) * tan(pi/5) ),
{
have : tan(3*pi/4) = tan((19*pi/20) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_702 : -sin(-pi/12)**2 + cos(11435*pi/12)**2=cos(3121*pi/6):=
begin
have : -sin(-pi / 12) ** 2 + (-cos(11435 * pi / 12)) ** 2 = -sin(-pi/12)**2 + cos(11435*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/12) = -cos(11435*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/12) (476),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(-pi/12) ** 2 + cos(-pi/12) ** 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(3121*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (260),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_703 (h0 : cos(3*pi/4)≠ 0) : sin(5649*pi/4)/cos(3*pi/4)=- 1:=
begin
have : sin(3*pi/4) = sin(5649*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (706),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = sin(3*pi/4) / cos(3*pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_704 : -cos(-2373*pi/4)=sqrt( 2 ) / 2:=
begin
have : -cos((-2373) * pi / 4) = -cos(-2373*pi/4),
{
field_simp at *,
},
have : sin(3931*pi/4) = -cos(-2373*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3931*pi/4) (194),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(3931*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (491),
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


lemma Trigo_number_generalization_step2_705 : sin(-383*pi/2)=1:=
begin
have : sin((-383) * pi / 2) = sin(-383*pi/2),
{
field_simp at *,
},
have : cos(718*pi) = sin(-383*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (718*pi) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(718*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (359),
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


lemma Trigo_number_generalization_step2_706 : -tan(1285*pi/4)=- 1:=
begin
have : tan(915*pi/4) = -tan(1285*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (915*pi/4) (550),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = tan(915*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (3*pi/4) (228),
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


lemma Trigo_number_generalization_step2_707 (h0 : cos(3*pi/8)≠ 0) (h1 : (1-tan(3*pi/8)**2)≠ 0) (h2 : tan(6665*pi/8)≠ 0) (h3 : ((1-1/tan(6665*pi/8)**2)*tan(6665*pi/8))≠ 0) (h4 : (1-(1/tan(6665*pi/8))**2)≠ 0) : 2/((1 - 1/tan(6665*pi/8)**2)*tan(6665*pi/8))=- 1:=
begin
have : 2 * (1 / tan(6665 * pi / 8)) / (1 - (1 / tan(6665 * pi / 8)) ** 2) = 2/((1 - 1/tan(6665*pi/8)**2)*tan(6665*pi/8)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/8) = 1 / tan(6665*pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/8) (833),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 2 * tan(3*pi/8) / ( 1 - tan(3*pi/8) ** 2 ),
{
have : tan(3*pi/4) = tan(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_708 : cos(-1411*pi/2)=2 * sin(pi) * cos(pi):=
begin
have : - -cos((-1411) * pi / 2) = cos(-1411*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1179*pi) = -cos(-1411*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1179*pi) (236),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(1179*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (588),
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


lemma Trigo_number_generalization_step2_709 (h0 : cos((-pi/2)/2)≠ 0) (h1 : (1+cos(-pi/2))≠ 0) (h2 : (cos(-pi/2)+1)≠ 0) (h3 : (sin(1184*pi)+1)≠ 0) : sin(-pi/2)/(sin(1184*pi) + 1)=- 1 / tan(45*pi/4):=
begin
have : cos(-pi/2) = sin(1184*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (592),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) / (1 + cos(-pi / 2)) = sin(-pi/2)/(cos(-pi/2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = sin(-pi/2) / ( 1 + cos(-pi/2) ),
{
have : tan(-pi/4) = tan((-pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = - 1 / tan(45*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/4) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_710 : sin(pi/3)*cos(3479*pi/2) - sin(3479*pi/2)*cos(pi/3)=1 / 2:=
begin
have : -(sin(3479 * pi / 2) * cos(pi / 3) - sin(pi / 3) * cos(3479 * pi / 2)) = sin(pi/3)*cos(3479*pi/2) - sin(3479*pi/2)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(10435*pi/6) = sin(3479*pi/2) * cos(pi/3) - sin(pi/3) * cos(3479*pi/2),
{
have : sin(10435*pi/6) = sin((3479*pi/2) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(10435*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (869),
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


lemma Trigo_number_generalization_step2_711 : (-cos(9497*pi/12)**2 + cos(pi/12)**2)*cos(-pi/6)=cos(pi/3) / 2 + cos(0) / 2:=
begin
have : (-(-cos(9497 * pi / 12)) ** 2 + cos(pi / 12) ** 2) * cos(-pi / 6) = (-cos(9497*pi/12)**2 + cos(pi/12)**2)*cos(-pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(9497*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (395),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi/6) * cos(-pi/6) = cos(pi/3) / 2 + cos(0) / 2,
{
rw cos_mul_cos,
have : cos((pi/6) + (-pi/6)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (-pi/6)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_712 : 2*sin(pi/2)*sin(5*pi/4)*cos(pi/2) + cos(pi)*cos(5*pi/4)=sqrt( 2 ) / 2:=
begin
have : 2 * sin(pi / 2) * cos(pi / 2) * sin(5 * pi / 4) + cos(pi) * cos(5 * pi / 4) = 2*sin(pi/2)*sin(5*pi/4)*cos(pi/2) + cos(pi)*cos(5*pi/4),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 4) * sin(pi) + cos(5 * pi / 4) * cos(pi) = sin(pi)*sin(5*pi/4) + cos(pi)*cos(5*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(5*pi/4) * sin(pi) + cos(5*pi/4) * cos(pi),
{
have : cos(pi/4) = cos((5*pi/4) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_713 (h0 : cos((pi/2)/2)≠ 0) (h1 : sin(pi/2)≠ 0) (h2 : sin(3289*pi/2)≠ 0) : (1 - cos(pi/2))/sin(3289*pi/2)=1:=
begin
have : sin(pi/2) = sin(3289*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (822),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = ( 1 - cos(pi/2) ) / sin(pi/2),
{
have : tan(pi/4) = tan((pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_714 : -cos(1333*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(20693*pi/12) = -cos(1333*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (20693*pi/12) (917),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(20693*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (862),
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


lemma Trigo_number_generalization_step2_715 (h0 : cos(pi)≠ 0) : -cos(897*pi/2)/cos(pi)=0:=
begin
have : sin(pi) = -cos(897*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (224),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_716 : sin(709*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(691*pi/3) = sin(709*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (691*pi/3) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(691*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (115),
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


lemma Trigo_number_generalization_step2_717 : sin(1847*pi)*cos(7*pi/18) + cos(-pi/5) + sin(7*pi/18)*sin(pi/2)=2 * cos(-2*pi/45) * cos(-7*pi/45):=
begin
have : cos(7 * pi / 18) * sin(1847 * pi) + cos(-pi / 5) + sin(7 * pi / 18) * sin(pi / 2) = sin(1847*pi)*cos(7*pi/18) + cos(-pi/5) + sin(7*pi/18)*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(1847*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (923),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi / 5) + (sin(7 * pi / 18) * sin(pi / 2) + cos(7 * pi / 18) * cos(pi / 2)) = cos(7*pi/18)*cos(pi/2) + cos(-pi/5) + sin(7*pi/18)*sin(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = sin(7*pi/18) * sin(pi/2) + cos(7*pi/18) * cos(pi/2),
{
have : cos(-pi/9) = cos((7*pi/18) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) + cos(-pi/9) = 2 * cos(-2*pi/45) * cos(-7*pi/45),
{
rw cos_add_cos,
have : cos(((-pi/5) + (-pi/9))/2) = cos(-7*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/5) - (-pi/9))/2) = cos(-2*pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_718 (h0 : cos((pi/6)/2)≠ 0) (h1 : sin(pi/6)≠ 0) : (1 - cos(3347*pi/6))/sin(pi/6)=2 - sqrt( 3 ):=
begin
have : cos(pi/6) = cos(3347*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (279),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( 1 - cos(pi/6) ) / sin(pi/6),
{
have : tan(pi/12) = tan((pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_719 : sin(pi/5) ** 2=-2*sin(54671*pi/30)**3 + 1/2 + 3*sin(54671*pi/30)/2:=
begin
have : (-2) * sin(54671 * pi / 30) ** 3 + 1 / 2 + 3 * sin(54671 * pi / 30) / 2 = -2*sin(54671*pi/30)**3 + 1/2 + 3*sin(54671*pi/30)/2,
{
field_simp at *,
},
have : cos(2*pi/15) = sin(54671*pi/30),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/15) (911),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 / 2 - (4 * cos(2 * pi / 15) ** 3 - 3 * cos(2 * pi / 15)) / 2 = -2*cos(2*pi/15)**3 + 1/2 + 3*cos(2*pi/15)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/5) = 4 * cos(2*pi/15) ** 3 - 3 * cos(2*pi/15),
{
have : cos(2*pi/5) = cos(3*(2*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/5) ** 2 = 1 / 2 - cos(2*pi/5) / 2,
{
have : cos(2*pi/5) = cos(2*(pi/5)),
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


lemma Trigo_number_generalization_step2_720 : cos(pi)*cos(3031*pi/2) - sin(pi)*sin(3031*pi/2)=0:=
begin
have : -sin(3031 * pi / 2) * sin(pi) + cos(3031 * pi / 2) * cos(pi) = cos(pi)*cos(3031*pi/2) - sin(pi)*sin(3031*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3033*pi/2) = -sin(3031*pi/2) * sin(pi) + cos(3031*pi/2) * cos(pi),
{
have : cos(3033*pi/2) = cos((3031*pi/2) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(3033*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (757),
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


lemma Trigo_number_generalization_step2_721 : cos(-pi/2) - sin(3251*pi/3)=2 * cos(-pi/6) * cos(-pi/3):=
begin
have : cos(-pi / 2) + -sin(3251 * pi / 3) = cos(-pi/2) - sin(3251*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1964*pi/3) = -sin(3251*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1964*pi/3) (214),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(1964*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (327),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) + cos(-pi/6) = 2 * cos(-pi/6) * cos(-pi/3),
{
rw cos_add_cos,
have : cos(((-pi/2) + (-pi/6))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (-pi/6))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_722 : 3*sin(-2*pi/15) - 4*sin(-2*pi/15)**3=2*(-3*cos(-pi/15) + 4*cos(-pi/15)**3)*sin(-pi/5):=
begin
have : (-4) * sin((-2) * pi / 15) ** 3 + 3 * sin((-2) * pi / 15) = 3*sin(-2*pi/15) - 4*sin(-2*pi/15)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/5) = -4 * sin(-2*pi/15) ** 3 + 3 * sin(-2*pi/15),
{
have : sin(-2*pi/5) = sin(3*(-2*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 5) * (4 * cos(-pi / 15) ** 3 - 3 * cos(-pi / 15)) = 2*(-3*cos(-pi/15) + 4*cos(-pi/15)**3)*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) = 4 * cos(-pi/15) ** 3 - 3 * cos(-pi/15),
{
have : cos(-pi/5) = cos(3*(-pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/5) = 2 * sin(-pi/5) * cos(-pi/5),
{
have : sin(-2*pi/5) = sin(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_723 : (-sin(pi/6)*cos(13*pi/42) + (-4*sin(13*pi/126)**3 + 3*sin(13*pi/126))*cos(pi/6))*sin(-pi/6)=cos(-13*pi/42) / 2 - cos(-pi/42) / 2:=
begin
have : (-sin(pi / 6) * cos(13 * pi / 42) + ((-4) * sin(13 * pi / 126) ** 3 + 3 * sin(13 * pi / 126)) * cos(pi / 6)) * sin(-pi / 6) = (-sin(pi/6)*cos(13*pi/42) + (-4*sin(13*pi/126)**3 + 3*sin(13*pi/126))*cos(pi/6))*sin(-pi/6),
{
field_simp at *,
},
have : sin(13*pi/42) = -4 * sin(13*pi/126) ** 3 + 3 * sin(13*pi/126),
{
have : sin(13*pi/42) = sin(3*(13*pi/126)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 6) * (sin(13 * pi / 42) * cos(pi / 6) - sin(pi / 6) * cos(13 * pi / 42)) = (-sin(pi/6)*cos(13*pi/42) + sin(13*pi/42)*cos(pi/6))*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(13*pi/42) * cos(pi/6) - sin(pi/6) * cos(13*pi/42),
{
have : sin(pi/7) = sin((13*pi/42) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * sin(pi/7) = cos(-13*pi/42) / 2 - cos(-pi/42) / 2,
{
rw sin_mul_sin,
have : cos((-pi/6) + (pi/7)) = cos(-pi/42),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (pi/7)) = cos(-13*pi/42),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_724 : 1 - cos(15011*pi/9)**2=1 / 2 - cos(-2*pi/9) / 2:=
begin
have : cos(-pi/9) = cos(15011*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/9) (834),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) ** 2 = 1 - cos(-pi/9) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) ** 2 = 1 / 2 - cos(-2*pi/9) / 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
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


lemma Trigo_number_generalization_step2_725 : -4*sin(pi/9)**3 + 3*sin(pi/9)=2*(-3*cos(pi/18) + 4*cos(pi/18)**3)*sin(pi/6):=
begin
have : (-4) * sin(pi / 9) ** 3 + 3 * sin(pi / 9) = -4*sin(pi/9)**3 + 3*sin(pi/9),
{
field_simp at *,
},
have : sin(pi/3) = -4 * sin(pi/9) ** 3 + 3 * sin(pi/9),
{
have : sin(pi/3) = sin(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 6) * (4 * cos(pi / 18) ** 3 - 3 * cos(pi / 18)) = 2*(-3*cos(pi/18) + 4*cos(pi/18)**3)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_726 (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan(-pi/6)*tan(-pi/2))≠ 0) (h3 : (1+tan(-pi/2)*tan(-pi/6))≠ 0) (h4 : cos(-7*pi/24)≠ 0) (h5 : cos(-pi/8)≠ 0) (h6 : (1+tan((-7)*pi/24)*tan(-pi/8))≠ 0) (h7 : (tan(-7*pi/24)*tan(-pi/8)+1)≠ 0) (h8 : (1+tan(-pi/2)*((tan((-7)*pi/24)-tan(-pi/8))/(1+tan((-7)*pi/24)*tan(-pi/8))))≠ 0) (h9 : (1+(tan(-7*pi/24)-tan(-pi/8))*tan(-pi/2)/(tan(-7*pi/24)*tan(-pi/8)+1))≠ 0) : ((tan(-7*pi/24) - tan(-pi/8))/(tan(-7*pi/24)*tan(-pi/8) + 1) - tan(-pi/2))/(1 + (tan(-7*pi/24) - tan(-pi/8))*tan(-pi/2)/(tan(-7*pi/24)*tan(-pi/8) + 1))=sqrt( 3 ):=
begin
have : ((tan((-7) * pi / 24) - tan(-pi / 8)) / (1 + tan((-7) * pi / 24) * tan(-pi / 8)) - tan(-pi / 2)) / (1 + tan(-pi / 2) * ((tan((-7) * pi / 24) - tan(-pi / 8)) / (1 + tan((-7) * pi / 24) * tan(-pi / 8)))) = ((tan(-7*pi/24) - tan(-pi/8))/(tan(-7*pi/24)*tan(-pi/8) + 1) - tan(-pi/2))/(1 + (tan(-7*pi/24) - tan(-pi/8))*tan(-pi/2)/(tan(-7*pi/24)*tan(-pi/8) + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = ( tan(-7*pi/24) - tan(-pi/8) ) / ( 1 + tan(-7*pi/24) * tan(-pi/8) ),
{
have : tan(-pi/6) = tan((-7*pi/24) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-pi / 6) - tan(-pi / 2)) / (1 + tan(-pi / 6) * tan(-pi / 2)) = (tan(-pi/6) - tan(-pi/2))/(1 + tan(-pi/2)*tan(-pi/6)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( tan(-pi/6) - tan(-pi/2) ) / ( 1 + tan(-pi/6) * tan(-pi/2) ),
{
have : tan(pi/3) = tan((-pi/6) - (-pi/2)),
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


lemma Trigo_number_generalization_step2_727 : 1 - 2*cos(20197*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/24) = cos(20197*pi/24),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/24) (420),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = 1 - 2 * sin(pi/24) ** 2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_728 : sin(-pi) - sin(pi/4)=(-6*sin(10547*pi/8) + 8*sin(10547*pi/8)**3)*sin(-5*pi/8):=
begin
have : 2 * ((-3) * sin(10547 * pi / 8) + 4 * sin(10547 * pi / 8) ** 3) * sin((-5) * pi / 8) = (-6*sin(10547*pi/8) + 8*sin(10547*pi/8)**3)*sin(-5*pi/8),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = sin(10547*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/8) (659),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin((-5) * pi / 8) * (4 * cos(-pi / 8) ** 3 - 3 * cos(-pi / 8)) = 2*(-3*cos(-pi/8) + 4*cos(-pi/8)**3)*sin(-5*pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-3*pi/8) = 4 * cos(-pi/8) ** 3 - 3 * cos(-pi/8),
{
have : cos(-3*pi/8) = cos(3*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) - sin(pi/4) = 2 * sin(-5*pi/8) * cos(-3*pi/8),
{
rw sin_sub_sin,
have : cos(((-pi) + (pi/4))/2) = cos(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (pi/4))/2) = sin(-5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_729 : -sin(2*pi/63)*cos(pi/7) + sin(pi/7)*cos(2*pi/63) + sin(pi/6)=sin(pi/9) + sin(pi/6):=
begin
have : sin(pi / 6) - (sin(2 * pi / 63) * cos(pi / 7) - sin(pi / 7) * cos(2 * pi / 63)) = -sin(2*pi/63)*cos(pi/7) + sin(pi/7)*cos(2*pi/63) + sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(2*pi/63) * cos(pi/7) - sin(pi/7) * cos(2*pi/63),
{
have : sin(-pi/9) = sin((2*pi/63) - (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sin(pi / 9) / 2 + sin(pi / 6) / 2) = sin(pi/9) + sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/36) * cos(pi/36) = sin(pi/9) / 2 + sin(pi/6) / 2,
{
rw sin_mul_cos,
have : sin((5*pi/36) + (pi/36)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((5*pi/36) - (pi/36)) = sin(pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(5*pi/36) * cos(pi/36)) = 2*sin(5*pi/36)*cos(pi/36),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/6) - sin(-pi/9) = 2 * sin(5*pi/36) * cos(pi/36),
{
rw sin_sub_sin,
have : cos(((pi/6) + (-pi/9))/2) = cos(pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (-pi/9))/2) = sin(5*pi/36),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_730 : cos(-3249*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -cos((-3249) * pi / 4) = cos(-3249*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(4127*pi/4) = -cos(-3249*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4127*pi/4) (109),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = -sin(4127*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3*pi/4) (515),
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


lemma Trigo_number_generalization_step2_731 : sin(-pi/7)*cos(4378*pi/21) + sin(4378*pi/21)*cos(-pi/7)=sqrt( 3 ) / 2:=
begin
have : sin(4378 * pi / 21) * cos(-pi / 7) + sin(-pi / 7) * cos(4378 * pi / 21) = sin(-pi/7)*cos(4378*pi/21) + sin(4378*pi/21)*cos(-pi/7),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(625*pi/3) = sin(4378*pi/21) * cos(-pi/7) + sin(-pi/7) * cos(4378*pi/21),
{
have : sin(625*pi/3) = sin((4378*pi/21) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(625*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (104),
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


lemma Trigo_number_generalization_step2_732 : -sin(1367*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(4073*pi/4) = -sin(1367*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (4073*pi/4) (680),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(4073*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (509),
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


lemma Trigo_number_generalization_step2_733 (h0 : cos(3277*pi/4)≠ 0) : sin(3277*pi/4)/cos(3277*pi/4)=1:=
begin
have : tan(3277*pi/4) = sin(3277*pi/4) / cos(3277*pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = tan(3277*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (pi/4) (819),
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


lemma Trigo_number_generalization_step2_734 (h0 : cos(pi/3)≠ 0) (h1 : tan(7027*pi/6)≠ 0) : sin(pi/3)/cos(pi/3)=1/tan(7027*pi/6):=
begin
have : tan(3109*pi/6) = tan(7027*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (3109*pi/6) (653),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(3109*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (518),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_735 : cos(3432*pi/5)=1 - 2*sin(-pi/5)**2:=
begin
have : cos(-2*pi/5) = cos(3432*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi/5) (343),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (1 - sin(-pi / 5) ** 2) - 1 = 1 - 2*sin(-pi/5)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) ** 2 = 1 - sin(-pi/5) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/5) = 2 * cos(-pi/5) ** 2 - 1,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_736 : sin(3671*pi/8)=- sin(7663*pi/8):=
begin
have : sin(1175*pi/8) = sin(3671*pi/8),
{
rw sin_eq_sin_add_int_mul_two_pi (1175*pi/8) (156),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = sin(1175*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/8) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = - sin(7663*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/8) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_737 : 1 - 2*sin(2551*pi/12)**2=- sqrt( 3 ) / 2:=
begin
have : sin(5*pi/12) = sin(2551*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/12) (106),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_738 : -sin(139*pi/2)**2 + cos(139*pi/2)**2=- cos(1904*pi):=
begin
have : cos(139*pi) = -sin(139*pi/2) ** 2 + cos(139*pi/2) ** 2,
{
have : cos(139*pi) = cos(2*(139*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(139*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(1904*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (952),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_739 : -tan(173*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(3037*pi/6) = -tan(173*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3037*pi/6) (535),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(3037*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (506),
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


lemma Trigo_number_generalization_step2_740 (h0 : cos(pi/24)≠ 0) (h1 : (1-tan(pi/24)**2)≠ 0) (h2 : (1-((-1)/tan(1861*pi/24))**2)≠ 0) (h3 : ((1-1/tan(1861*pi/24)**2)*tan(1861*pi/24))≠ 0) (h4 : tan(1861*pi/24)≠ 0) : -2/((1 - 1/tan(1861*pi/24)**2)*tan(1861*pi/24))=2 - sqrt( 3 ):=
begin
have : 2 * ((-1) / tan(1861 * pi / 24)) / (1 - ((-1) / tan(1861 * pi / 24)) ** 2) = -2/((1 - 1/tan(1861*pi/24)**2)*tan(1861*pi/24)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/24) = -1 / tan(1861*pi/24),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/24) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 * tan(pi/24) / ( 1 - tan(pi/24) ** 2 ),
{
have : tan(pi/12) = tan(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_741 : -3*sin(34175*pi/54) + 4*sin(34175*pi/54)**3=sin(pi) * sin(pi/9) + cos(pi) * cos(pi/9):=
begin
have : -((-4) * sin(34175 * pi / 54) ** 3 + 3 * sin(34175 * pi / 54)) = -3*sin(34175*pi/54) + 4*sin(34175*pi/54)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(34175*pi/18) = -4 * sin(34175*pi/54) ** 3 + 3 * sin(34175*pi/54),
{
have : sin(34175*pi/18) = sin(3*(34175*pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi/9) = -sin(34175*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/9) (949),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi/9) = sin(pi) * sin(pi/9) + cos(pi) * cos(pi/9),
{
have : cos(8*pi/9) = cos((pi) - (pi/9)),
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


lemma Trigo_number_generalization_step2_742 : -cos(-pi/9)*cos(16135*pi/18) - sin(-pi/9)*sin(16135*pi/18)=0:=
begin
have : -(sin(16135 * pi / 18) * sin(-pi / 9) + cos(16135 * pi / 18) * cos(-pi / 9)) = -cos(-pi/9)*cos(16135*pi/18) - sin(-pi/9)*sin(16135*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1793*pi/2) = sin(16135*pi/18) * sin(-pi/9) + cos(16135*pi/18) * cos(-pi/9),
{
have : cos(1793*pi/2) = cos((16135*pi/18) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(1793*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (448),
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


lemma Trigo_number_generalization_step2_743 (h0 : cos((-4*pi)/2)≠ 0) (h1 : (1+cos((-4)*pi))≠ 0) (h2 : (1+cos(-4*pi))≠ 0) (h3 : cos(8353*pi/9)≠ 0) (h4 : cos(pi/9)≠ 0) (h5 : (tan(pi/9)*tan(8353*pi/9)+1)≠ 0) (h6 : (1+tan(8353*pi/9)*tan(pi/9))≠ 0) : sin(-4*pi)/(1 + cos(-4*pi))=(-tan(pi/9) + tan(8353*pi/9))/(tan(pi/9)*tan(8353*pi/9) + 1):=
begin
have : (tan(8353 * pi / 9) - tan(pi / 9)) / (1 + tan(8353 * pi / 9) * tan(pi / 9)) = (-tan(pi/9) + tan(8353*pi/9))/(tan(pi/9)*tan(8353*pi/9) + 1),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(928*pi) = ( tan(8353*pi/9) - tan(pi/9) ) / ( 1 + tan(8353*pi/9) * tan(pi/9) ),
{
have : tan(928*pi) = tan((8353*pi/9) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
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
have : tan(-2*pi) = tan(928*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (930),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_744 : -cos(-2242*pi/3)=1 / 2:=
begin
have : -cos((-2242) * pi / 3) = -cos(-2242*pi/3),
{
field_simp at *,
},
have : sin(10901*pi/6) = -cos(-2242*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (10901*pi/6) (534),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(10901*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (908),
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


lemma Trigo_number_generalization_step2_745 : -sin(8*pi/15)/2 + sin(pi/5)/2 + sin(11*pi/30)*cos(pi/6)=- sin(4059*pi/5):=
begin
have : -(-sin(pi / 5) / 2 + sin(8 * pi / 15) / 2) + sin(11 * pi / 30) * cos(pi / 6) = -sin(8*pi/15)/2 + sin(pi/5)/2 + sin(11*pi/30)*cos(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(11*pi/30) = -sin(pi/5) / 2 + sin(8*pi/15) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((11*pi/30) + (pi/6)) = sin(8*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : sin((11*pi/30) - (pi/6)) = sin(pi/5),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(pi/6) * cos(11*pi/30)) = -sin(pi/6)*cos(11*pi/30),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(11 * pi / 30) * cos(pi / 6) - sin(pi / 6) * cos(11 * pi / 30) = -sin(pi/6)*cos(11*pi/30) + sin(11*pi/30)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = sin(11*pi/30) * cos(pi/6) - sin(pi/6) * cos(11*pi/30),
{
have : sin(pi/5) = sin((11*pi/30) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = - sin(4059*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/5) (406),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_746 : (-4*sin(pi/15)**3 + 3*sin(pi/15))**2 + cos(5749*pi/5)**2=1:=
begin
have : ((-4) * sin(pi / 15) ** 3 + 3 * sin(pi / 15)) ** 2 + cos(5749 * pi / 5) ** 2 = (-4*sin(pi/15)**3 + 3*sin(pi/15))**2 + cos(5749*pi/5)**2,
{
field_simp at *,
},
have : sin(pi/5) = -4 * sin(pi/15) ** 3 + 3 * sin(pi/15),
{
have : sin(pi/5) = sin(3*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = cos(5749*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/5) (575),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) ** 2 + cos(pi/5) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_747 (h0 : cos(434*pi)≠ 0) : sin(2*pi)/cos(434*pi)=-tan(700*pi):=
begin
have : tan(2*pi) = -tan(700*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (702),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = cos(434*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (216),
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


lemma Trigo_number_generalization_step2_748 : sin(-49*pi/8)*cos(-pi/8) + sin(-pi/8)*cos(1737*pi/8)=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : sin((-49) * pi / 8) * cos(-pi / 8) - sin(-pi / 8) * -cos(1737 * pi / 8) = sin(-49*pi/8)*cos(-pi/8) + sin(-pi/8)*cos(1737*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-49*pi/8) = -cos(1737*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-49*pi/8) (105),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-49) * pi / 8) * cos(-pi / 8) - sin(-pi / 8) * cos((-49) * pi / 8) = sin(-49*pi/8)*cos(-pi/8) - sin(-pi/8)*cos(-49*pi/8),
{
field_simp at *,
},
have : sin(-6*pi) = sin(-49*pi/8) * cos(-pi/8) - sin(-pi/8) * cos(-49*pi/8),
{
have : sin(-6*pi) = sin((-49*pi/8) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
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


lemma Trigo_number_generalization_step2_749 : sin(-161*pi/72)*cos(-2*pi) + sin(-17*pi/72)/2 - sin(-305*pi/72)/2=sin(-pi/9) * cos(pi/8) - sin(pi/8) * cos(-pi/9):=
begin
have : sin((-161) * pi / 72) * cos((-2) * pi) - (-sin((-17) * pi / 72) / 2 + sin((-305) * pi / 72) / 2) = sin(-161*pi/72)*cos(-2*pi) + sin(-17*pi/72)/2 - sin(-305*pi/72)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-161*pi/72) = -sin(-17*pi/72) / 2 + sin(-305*pi/72) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-161*pi/72) + (-2*pi)) = sin(-305*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-161*pi/72) - (-2*pi)) = sin(-17*pi/72),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-2*pi) * cos(-161*pi/72)) = sin(-2*pi)*cos(-161*pi/72),
{
ring,
},
have : sin((-161) * pi / 72) * cos((-2) * pi) - sin((-2) * pi) * cos((-161) * pi / 72) = sin(-161*pi/72)*cos(-2*pi) - sin(-2*pi)*cos(-161*pi/72),
{
field_simp at *,
},
have : sin(-17*pi/72) = sin(-161*pi/72) * cos(-2*pi) - sin(-2*pi) * cos(-161*pi/72),
{
have : sin(-17*pi/72) = sin((-161*pi/72) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-17*pi/72) = sin(-pi/9) * cos(pi/8) - sin(pi/8) * cos(-pi/9),
{
have : sin(-17*pi/72) = sin((-pi/9) - (pi/8)),
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


lemma Trigo_number_generalization_step2_750 : sin(11*pi/6)*cos(2*pi) - sin(2*pi)*cos(11065*pi/6)=cos(2306*pi/3):=
begin
have : cos(11*pi/6) = cos(11065*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (11*pi/6) (923),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(11*pi/6) * cos(2*pi) - sin(2*pi) * cos(11*pi/6),
{
have : sin(-pi/6) = sin((11*pi/6) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(2306*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (384),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_751 : -1 + 2*(-3*cos(pi/8) + 4*cos(pi/8)**3)**2=- sqrt( 2 ) / 2:=
begin
have : -1 + 2 * (4 * cos(pi / 8) ** 3 - 3 * cos(pi / 8)) ** 2 = -1 + 2*(-3*cos(pi/8) + 4*cos(pi/8)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = 4 * cos(pi/8) ** 3 - 3 * cos(pi/8),
{
have : cos(3*pi/8) = cos(3*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(3 * pi / 8) ** 2 - 1 = -1 + 2*cos(3*pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = 2 * cos(3*pi/8) ** 2 - 1,
{
have : cos(3*pi/4) = cos(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_752 : sin(-3*pi/28)=sin(-pi/4)*sin(23333*pi/14) + sin(-3*pi/28)/2 - sin(-11*pi/28)/2:=
begin
have : sin(-pi / 4) * sin(23333 * pi / 14) + (-sin((-11) * pi / 28) / 2 + sin((-3) * pi / 28) / 2) = sin(-pi/4)*sin(23333*pi/14) + sin(-3*pi/28)/2 - sin(-11*pi/28)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) * cos(-pi/4) = -sin(-11*pi/28) / 2 + sin(-3*pi/28) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/4) + (pi/7)) = sin(-3*pi/28),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/4) - (pi/7)) = sin(-11*pi/28),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : (sin(pi/7) * cos(-pi/4)) = sin(pi/7)*cos(-pi/4),
{
ring,
},
have : cos(pi/7) = sin(23333*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/7) (833),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/28) = sin(-pi/4) * cos(pi/7) + sin(pi/7) * cos(-pi/4),
{
have : sin(-3*pi/28) = sin((-pi/4) + (pi/7)),
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


lemma Trigo_number_generalization_step2_753 : sin(-pi/7)=-3*sin(26144*pi/21) + 4*sin(26144*pi/21)**3:=
begin
have : (-3) * sin(26144 * pi / 21) + 4 * sin(26144 * pi / 21) ** 3 = -3*sin(26144*pi/21) + 4*sin(26144*pi/21)**3,
{
field_simp at *,
},
have : cos(14513*pi/42) = sin(26144*pi/21),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (14513*pi/42) (795),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 4 * cos(14513 * pi / 42) ** 3 - 3 * cos(14513 * pi / 42) = -3*cos(14513*pi/42) + 4*cos(14513*pi/42)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(14513*pi/14) = 4 * cos(14513*pi/42) ** 3 - 3 * cos(14513*pi/42),
{
have : cos(14513*pi/14) = cos(3*(14513*pi/42)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) = cos(14513*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (518),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_754 : 3*cos(5662*pi/9) - 4*cos(5662*pi/9)**3=cos(4837*pi/3):=
begin
have : -(4 * cos(5662 * pi / 9) ** 3 - 3 * cos(5662 * pi / 9)) = 3*cos(5662*pi/9) - 4*cos(5662*pi/9)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5662*pi/3) = 4 * cos(5662*pi/9) ** 3 - 3 * cos(5662*pi/9),
{
have : cos(5662*pi/3) = cos(3*(5662*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(5662*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (943),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(4837*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (806),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_755 : -sin(10267*pi/24)**2 + cos(10267*pi/24)**2=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(10267*pi/12) = -sin(10267*pi/24) ** 2 + cos(10267*pi/24) ** 2,
{
have : cos(10267*pi/12) = cos(2*(10267*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(10267*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (427),
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


lemma Trigo_number_generalization_step2_756 (h0 : sin(pi/4)≠ 0) (h1 : (2*sin(pi/4))≠ 0) : cos(1522*pi)/(2*sin(pi/4))=sqrt( 2 ) / 2:=
begin
have : sin(pi/2) = cos(1522*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (761),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(pi/2) / ( 2 * sin(pi/4) ),
{
have : sin(pi/2) = sin(2*(pi/4)),
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_757 (h0 : cos(pi/3)≠ 0) (h1 : (1-tan(pi/3)**2)≠ 0) (h2 : cos((2*pi/3)/2)≠ 0) (h3 : sin(2*pi/3)≠ 0) (h4 : (1-((1-cos(2*pi/3))/sin(2*pi/3))**2)≠ 0) (h5 : ((-(1-cos(2*pi/3))**2/sin(2*pi/3)**2+1)*sin(2*pi/3))≠ 0) : 2*(1 - cos(2*pi/3))/((-(1 - cos(2*pi/3))**2/sin(2*pi/3)**2 + 1)*sin(2*pi/3))=- sqrt( 3 ):=
begin
have : 2 * ((1 - cos(2 * pi / 3)) / sin(2 * pi / 3)) / (1 - ((1 - cos(2 * pi / 3)) / sin(2 * pi / 3)) ** 2) = 2*(1 - cos(2*pi/3))/((-(1 - cos(2*pi/3))**2/sin(2*pi/3)**2 + 1)*sin(2*pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( 1 - cos(2*pi/3) ) / sin(2*pi/3),
{
have : tan(pi/3) = tan((2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = 2 * tan(pi/3) / ( 1 - tan(pi/3) ** 2 ),
{
have : tan(2*pi/3) = tan(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_758 : 1 - cos(-pi/9)**2=-cos(-11*pi/9)*cos(pi)/2 + sin(-11*pi/9)*sin(pi)/2 + 1/2:=
begin
have : sin(-pi/9) ** 2 = 1 - cos(-pi/9) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 - (-sin((-11) * pi / 9) * sin(pi) + cos((-11) * pi / 9) * cos(pi)) / 2 = -cos(-11*pi/9)*cos(pi)/2 + sin(-11*pi/9)*sin(pi)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/9) = -sin(-11*pi/9) * sin(pi) + cos(-11*pi/9) * cos(pi),
{
have : cos(-2*pi/9) = cos((-11*pi/9) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) ** 2 = 1 / 2 - cos(-2*pi/9) / 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
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


lemma Trigo_number_generalization_step2_759 (h0 : cos(7*pi/24)≠ 0) (h1 : cos(pi/6)≠ 0) (h2 : (tan(pi/6)*tan(7*pi/24)+1)≠ 0) (h3 : (1+tan(7*pi/24)*tan(pi/6))≠ 0) (h4 : (-tan(7*pi/24)/tan(2999*pi/3)+1)≠ 0) (h5 : tan(2999*pi/3)≠ 0) (h6 : ((-1)/tan(2999*pi/3)*tan(7*pi/24)+1)≠ 0) : (1/tan(2999*pi/3) + tan(7*pi/24))/(-tan(7*pi/24)/tan(2999*pi/3) + 1)=- tan(2135*pi/8):=
begin
have : (-((-1) / tan(2999 * pi / 3)) + tan(7 * pi / 24)) / ((-1) / tan(2999 * pi / 3) * tan(7 * pi / 24) + 1) = (1/tan(2999*pi/3) + tan(7*pi/24))/(-tan(7*pi/24)/tan(2999*pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -1 / tan(2999*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(7 * pi / 24) - tan(pi / 6)) / (1 + tan(7 * pi / 24) * tan(pi / 6)) = (-tan(pi/6) + tan(7*pi/24))/(tan(pi/6)*tan(7*pi/24) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = ( tan(7*pi/24) - tan(pi/6) ) / ( 1 + tan(7*pi/24) * tan(pi/6) ),
{
have : tan(pi/8) = tan((7*pi/24) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = - tan(2135*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/8) (267),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_760 : sin(6713*pi/4)=sin(7139*pi/4):=
begin
have : cos(pi/4) = sin(6713*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (839),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(7139 * pi / 4) = sin(7139*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1839*pi/4) = -sin(7139*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1839*pi/4) (662),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = - sin(1839*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (229),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_761 : -sin(-5499*pi/8)/2 - sin(5495*pi/8)/2=- sin(pi/8) / 2 + sin(-3*pi/8) / 2:=
begin
have : -(sin((-5499) * pi / 8) / 2 + sin(5495 * pi / 8) / 2) = -sin(-5499*pi/8)/2 - sin(5495*pi/8)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * cos(5497*pi/8) = sin(-5499*pi/8) / 2 + sin(5495*pi/8) / 2,
{
rw sin_mul_cos,
have : sin((-pi/4) + (5497*pi/8)) = sin(5495*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/4) - (5497*pi/8)) = sin(-5499*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(-pi/4) * cos(5497*pi/8)) = -sin(-pi/4)*cos(5497*pi/8),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(-pi / 4) * -cos(5497 * pi / 8) = -sin(-pi/4)*cos(5497*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = -cos(5497*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/8) (343),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * cos(-pi/8) = - sin(pi/8) / 2 + sin(-3*pi/8) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/8) + (-pi/4)) = sin(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/8) - (-pi/4)) = sin(pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_762 : -(3*sin(-pi/24) - 4*sin(-pi/24)**3)*cos(1968*pi)=sin(-9*pi/8) / 2 + sin(7*pi/8) / 2:=
begin
have : (3 * sin(-pi / 24) - 4 * sin(-pi / 24) ** 3) * -cos(1968 * pi) = -(3*sin(-pi/24) - 4*sin(-pi/24)**3)*cos(1968*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(1968*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (983),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(-pi / 24) ** 3 + 3 * sin(-pi / 24)) * cos(pi) = (3*sin(-pi/24) - 4*sin(-pi/24)**3)*cos(pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -4 * sin(-pi/24) ** 3 + 3 * sin(-pi/24),
{
have : sin(-pi/8) = sin(3*(-pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) * cos(pi) = sin(-9*pi/8) / 2 + sin(7*pi/8) / 2,
{
rw sin_mul_cos,
have : sin((-pi/8) + (pi)) = sin(7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/8) - (pi)) = sin(-9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_763 (h0 : cos(13*pi/36)≠ 0) (h1 : cos(pi/9)≠ 0) (h2 : (1+tan(13*pi/36)*tan(pi/9))≠ 0) (h3 : (tan(pi/9)*tan(13*pi/36)+1)≠ 0) (h4 : (-tan(7181*pi/9)*tan(13*pi/36)+1)≠ 0) (h5 : (-tan(13*pi/36)*tan(7181*pi/9)+1)≠ 0) : (tan(7181*pi/9) + tan(13*pi/36))/(-tan(13*pi/36)*tan(7181*pi/9) + 1)=1:=
begin
have : (- -tan(7181 * pi / 9) + tan(13 * pi / 36)) / (-tan(7181 * pi / 9) * tan(13 * pi / 36) + 1) = (tan(7181*pi/9) + tan(13*pi/36))/(-tan(13*pi/36)*tan(7181*pi/9) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = -tan(7181*pi/9),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/9) (798),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(13 * pi / 36) - tan(pi / 9)) / (1 + tan(13 * pi / 36) * tan(pi / 9)) = (-tan(pi/9) + tan(13*pi/36))/(tan(pi/9)*tan(13*pi/36) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = ( tan(13*pi/36) - tan(pi/9) ) / ( 1 + tan(13*pi/36) * tan(pi/9) ),
{
have : tan(pi/4) = tan((13*pi/36) - (pi/9)),
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


lemma Trigo_number_generalization_step2_764 : cos(-6*pi/5)*cos(8791*pi/5) - sin(-6*pi/5)*sin(pi/5)=1 - 2 * sin(-pi/2) ** 2:=
begin
have : cos((-6) * pi / 5) * cos(8791 * pi / 5) - sin((-6) * pi / 5) * sin(pi / 5) = cos(-6*pi/5)*cos(8791*pi/5) - sin(-6*pi/5)*sin(pi/5),
{
field_simp at *,
},
have : cos(pi/5) = cos(8791*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/5) (879),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-6) * pi / 5) * sin(pi / 5) + cos((-6) * pi / 5) * cos(pi / 5) = cos(-6*pi/5)*cos(pi/5) - sin(-6*pi/5)*sin(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(-6*pi/5) * sin(pi/5) + cos(-6*pi/5) * cos(pi/5),
{
have : cos(-pi) = cos((-6*pi/5) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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
rw this,
end


lemma Trigo_number_generalization_step2_765 (h0 : cos((-2*pi/5)/2)≠ 0) (h1 : (cos(-2*pi/5)+1)≠ 0) (h2 : (1+cos((-2)*pi/5))≠ 0) (h3 : (cos((-2)*pi/5)+1)≠ 0) : sin(5127*pi/5)/(cos(-2*pi/5) + 1)=- 1 / tan(1953*pi/10):=
begin
have : sin(5127 * pi / 5) / (cos((-2) * pi / 5) + 1) = sin(5127*pi/5)/(cos(-2*pi/5) + 1),
{
field_simp at *,
},
have : sin(-2*pi/5) = sin(5127*pi/5),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi/5) (512),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi / 5) / (1 + cos((-2) * pi / 5)) = sin(-2*pi/5)/(cos(-2*pi/5) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = sin(-2*pi/5) / ( 1 + cos(-2*pi/5) ),
{
have : tan(-pi/5) = tan((-2*pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = - 1 / tan(1953*pi/10),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/5) (195),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_766 : -cos(595*pi)=sin(-243*pi/2):=
begin
have : sin(pi/2) = -cos(595*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (297),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin((-243) * pi / 2) = sin(-243*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(1493*pi) = -sin(-243*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1493*pi) (685),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = - cos(1493*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (746),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_767 : (-sin(-pi/4)**2 + cos(-pi/4)**2)**2=1 - (3*sin(-pi/6) - 4*sin(-pi/6)**3)**2:=
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
have : 1 - ((-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6)) ** 2 = 1 - (3*sin(-pi/6) - 4*sin(-pi/6)**3)**2,
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
have : cos(-pi/2) ** 2 = 1 - sin(-pi/2) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step2_768 : -(-4*sin(pi/24)**3 + 3*sin(pi/24))*sin(4347*pi/4)=cos(-3*pi/8) / 2 - cos(-pi/8) / 2:=
begin
have : ((-4) * sin(pi / 24) ** 3 + 3 * sin(pi / 24)) * -sin(4347 * pi / 4) = -(-4*sin(pi/24)**3 + 3*sin(pi/24))*sin(4347*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -sin(4347*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (543),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 4) * ((-4) * sin(pi / 24) ** 3 + 3 * sin(pi / 24)) = (-4*sin(pi/24)**3 + 3*sin(pi/24))*sin(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -4 * sin(pi/24) ** 3 + 3 * sin(pi/24),
{
have : sin(pi/8) = sin(3*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * sin(pi/8) = cos(-3*pi/8) / 2 - cos(-pi/8) / 2,
{
rw sin_mul_sin,
have : cos((-pi/4) + (pi/8)) = cos(-pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/4) - (pi/8)) = cos(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_769 (h0 : cos(20401*pi/12)≠ 0) (h1 : (2*cos(20401*pi/12))≠ 0) : sin(20401*pi/6)/(2*cos(20401*pi/12))=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(20401*pi/12) = sin(20401*pi/6) / ( 2 * cos(20401*pi/12) ),
{
have : sin(20401*pi/6) = sin(2*(20401*pi/12)),
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
have : sin(pi/12) = sin(20401*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (850),
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


lemma Trigo_number_generalization_step2_770 : cos(1007*pi)**2=1 - cos(pi/2) ** 2:=
begin
have : (-cos(1007 * pi)) ** 2 = cos(1007*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(522*pi) = -cos(1007*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (522*pi) (242),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(522*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (261),
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


lemma Trigo_number_generalization_step2_771 (h0 : sin(-pi/6)≠ 0) (h1 : (2*sin(-pi/6))≠ 0) (h2 : (2*sin(-pi/6)**2)≠ 0) : -sin(10795*pi/6)=-1 + sin(-pi/3)**2/(2*sin(-pi/6)**2):=
begin
have : 2 * (sin(-pi / 3) / (2 * sin(-pi / 6))) ** 2 - 1 = -1 + sin(-pi/3)**2/(2*sin(-pi/6)**2),
{
field_simp at *,
ring,
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
have : cos(-pi/3) = -sin(10795*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (899),
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


lemma Trigo_number_generalization_step2_772 (h0 : tan(380*pi/3)≠ 0) (h1 : tan(616*pi/3)≠ 0) (h2 : -tan(616*pi/3)≠ 0) : 1/tan(616*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / -tan(616 * pi / 3) = 1/tan(616*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(380*pi/3) = -tan(616*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (380*pi/3) (332),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(380 * pi / 3) = -1/tan(380*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(380*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (126),
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


lemma Trigo_number_generalization_step2_773 (h0 : cos(2377*pi/9)≠ 0) (h1 : (2*cos(2377*pi/9))≠ 0) : -sin(4754*pi/9)/(2*cos(2377*pi/9))=- cos(14155*pi/18):=
begin
have : -(sin(4754 * pi / 9) / (2 * cos(2377 * pi / 9))) = -sin(4754*pi/9)/(2*cos(2377*pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2377*pi/9) = sin(4754*pi/9) / ( 2 * cos(2377*pi/9) ),
{
have : sin(4754*pi/9) = sin(2*(2377*pi/9)),
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
have : sin(-pi/9) = -sin(2377*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/9) (132),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = - cos(14155*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/9) (393),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_774 : 1 - sin(-pi/5)**2=cos(-pi/5)**2:=
begin
have : (2 * cos(-pi / 5) ** 2 - 1) / 2 + 1 / 2 = cos(-pi/5)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/5) = 2 * cos(-pi/5) ** 2 - 1,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) ** 2 = 1 - sin(-pi/5) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) ** 2 = cos(-2*pi/5) / 2 + 1 / 2,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
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


lemma Trigo_number_generalization_step2_775 : 1 - 2*sin(6157*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : cos(6157*pi/6) = 1 - 2 * sin(6157*pi/12) ** 2,
{
have : cos(6157*pi/6) = cos(2*(6157*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(6157*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (513),
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


lemma Trigo_number_generalization_step2_776 : cos(-9141*pi/8)=sin(12639*pi/8):=
begin
have : - -cos((-9141) * pi / 8) = cos(-9141*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(15293*pi/8) = -cos(-9141*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (15293*pi/8) (384),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -cos(15293*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (955),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(12639*pi/8),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/8) (790),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_777 : -cos(527*pi/2)=0:=
begin
have : cos(1913*pi/2) = cos(527*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (1913*pi/2) (610),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(1913*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (478),
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


lemma Trigo_number_generalization_step2_778 : sin(-pi/3)*cos(7*pi/3) - sin(7*pi/3)*cos(884*pi/3)=- sin(529*pi):=
begin
have : sin(-pi / 3) * cos(7 * pi / 3) + sin(7 * pi / 3) * -cos(884 * pi / 3) = sin(-pi/3)*cos(7*pi/3) - sin(7*pi/3)*cos(884*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(884*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (147),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 3) * cos(-pi / 3) + sin(-pi / 3) * cos(7 * pi / 3) = sin(-pi/3)*cos(7*pi/3) + sin(7*pi/3)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(7*pi/3) * cos(-pi/3) + sin(-pi/3) * cos(7*pi/3),
{
have : sin(2*pi) = sin((7*pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(529*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_779 (h0 : cos((1862*pi/3)/2)≠ 0) (h1 : sin(1862*pi/3)≠ 0) : -(1 - cos(1862*pi/3))/sin(1862*pi/3)=- sqrt( 3 ):=
begin
have : -((1 - cos(1862 * pi / 3)) / sin(1862 * pi / 3)) = -(1 - cos(1862*pi/3))/sin(1862*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(931*pi/3) = ( 1 - cos(1862*pi/3) ) / sin(1862*pi/3),
{
have : tan(931*pi/3) = tan((1862*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(931*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (311),
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


lemma Trigo_number_generalization_step2_780 (h0 : cos((pi/2)/2)≠ 0) (h1 : (cos(pi/2)+1)≠ 0) (h2 : (1+cos(pi/2))≠ 0) (h3 : (-sin(pi/9)*sin(7*pi/18)+cos(pi/9)*cos(7*pi/18)+1)≠ 0) (h4 : (-sin(7*pi/18)*sin(pi/9)+cos(7*pi/18)*cos(pi/9)+1)≠ 0) : sin(pi/2)/(-sin(pi/9)*sin(7*pi/18) + cos(pi/9)*cos(7*pi/18) + 1)=- tan(3291*pi/4):=
begin
have : sin(pi / 2) / (-sin(7 * pi / 18) * sin(pi / 9) + cos(7 * pi / 18) * cos(pi / 9) + 1) = sin(pi/2)/(-sin(pi/9)*sin(7*pi/18) + cos(pi/9)*cos(7*pi/18) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(7*pi/18) * sin(pi/9) + cos(7*pi/18) * cos(pi/9),
{
have : cos(pi/2) = cos((7*pi/18) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 2) / (1 + cos(pi / 2)) = sin(pi/2)/(cos(pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = sin(pi/2) / ( 1 + cos(pi/2) ),
{
have : tan(pi/4) = tan((pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = - tan(3291*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (823),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_781 : -cos(4059*pi/4)=- cos(5853*pi/4):=
begin
have : cos(2285*pi/4) = cos(4059*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2285*pi/4) (793),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(2285*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (285),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = - cos(5853*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (731),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_782 : sin(-pi/8) ** 2=1 - (-1 + 2*cos(23793*pi/16)**2)**2:=
begin
have : 1 - (-1 + 2 * (-cos(23793 * pi / 16)) ** 2) ** 2 = 1 - (-1 + 2*cos(23793*pi/16)**2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/16) = -cos(23793*pi/16),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/16) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - (2 * cos(-pi / 16) ** 2 - 1) ** 2 = 1 - (-1 + 2*cos(-pi/16)**2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = 2 * cos(-pi/16) ** 2 - 1,
{
have : cos(-pi/8) = cos(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) ** 2 = 1 - cos(-pi/8) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_783 : cos(-pi/7)*cos(6*pi/7) + sin(-pi/7)*cos(8395*pi/14)=- 1:=
begin
have : sin(6*pi/7) = cos(8395*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (6*pi/7) (300),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(6 * pi / 7) * sin(-pi / 7) + cos(6 * pi / 7) * cos(-pi / 7) = cos(-pi/7)*cos(6*pi/7) + sin(-pi/7)*sin(6*pi/7),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(6*pi/7) * sin(-pi/7) + cos(6*pi/7) * cos(-pi/7),
{
have : cos(pi) = cos((6*pi/7) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_784 (h0 : cos(2*pi/3)≠ 0) : (sin(pi/6)*cos(-pi/2) - sin(-pi/2)*cos(pi/6))/cos(2*pi/3)=- sqrt( 3 ):=
begin
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
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = sin(2*pi/3) / cos(2*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = - sqrt( 3 ),
{
rw tan_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_785 : 2*sin(-pi/4)*sin(-pi/24)*cos(-pi/24) + cos(-pi/4)*cos(-pi/12)=sqrt( 3 ) / 2:=
begin
have : sin(-pi / 4) * (2 * sin(-pi / 24) * cos(-pi / 24)) + cos(-pi / 4) * cos(-pi / 12) = 2*sin(-pi/4)*sin(-pi/24)*cos(-pi/24) + cos(-pi/4)*cos(-pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = 2 * sin(-pi/24) * cos(-pi/24),
{
have : sin(-pi/12) = sin(2*(-pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 12) * sin(-pi / 4) + cos(-pi / 12) * cos(-pi / 4) = sin(-pi/4)*sin(-pi/12) + cos(-pi/4)*cos(-pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(-pi/12) * sin(-pi/4) + cos(-pi/12) * cos(-pi/4),
{
have : cos(pi/6) = cos((-pi/12) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_786 : -1 + 2*(-1 + 2*cos(pi/28)**2)**2=cos(701*pi/7):=
begin
have : -1 + 2 * (2 * cos(pi / 28) ** 2 - 1) ** 2 = -1 + 2*(-1 + 2*cos(pi/28)**2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/14) = 2 * cos(pi/28) ** 2 - 1,
{
have : cos(pi/14) = cos(2*(pi/28)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 14) ** 2 - 1 = -1 + 2*cos(pi/14)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = 2 * cos(pi/14) ** 2 - 1,
{
have : cos(pi/7) = cos(2*(pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = cos(701*pi/7),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/7) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_787 (h0 : cos(-pi/9)≠ 0) (h1 : (2*cos(-pi/9))≠ 0) : -cos(1903*pi/4) + sin(-2*pi/9)/(2*cos(-pi/9))=2 * sin(-13*pi/72) * cos(5*pi/72):=
begin
have : -cos(1903 * pi / 4) + sin((-2) * pi / 9) / (2 * cos(-pi / 9)) = -cos(1903*pi/4) + sin(-2*pi/9)/(2*cos(-pi/9)),
{
field_simp at *,
},
have : sin(-pi/4) = -cos(1903*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (237),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi / 9) / (2 * cos(-pi / 9)) + sin(-pi / 4) = sin(-pi/4) + sin(-2*pi/9)/(2*cos(-pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(-2*pi/9) / ( 2 * cos(-pi/9) ),
{
have : sin(-2*pi/9) = sin(2*(-pi/9)),
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
have : sin(-pi/9) + sin(-pi/4) = 2 * sin(-13*pi/72) * cos(5*pi/72),
{
rw sin_add_sin,
have : sin(((-pi/9) + (-pi/4))/2) = sin(-13*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (-pi/4))/2) = cos(5*pi/72),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_788 (h0 : cos(890*pi)≠ 0) : -sin(890*pi)/cos(890*pi)=1 / tan(427*pi/2):=
begin
have : -(sin(890 * pi) / cos(890 * pi)) = -sin(890*pi)/cos(890*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(890*pi) = sin(890*pi) / cos(890*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = -tan(890*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (891),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(427*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (214),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_789 : -sin(5763*pi/14)=-sin(265*pi/14)**2 + cos(265*pi/14)**2:=
begin
have : cos(265*pi/7) = -sin(265*pi/14) ** 2 + cos(265*pi/14) ** 2,
{
have : cos(265*pi/7) = cos(2*(265*pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = -sin(5763*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (205),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = cos(265*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/7) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_790 : -sin(pi/3)*cos(11*pi/24) - sin(11*pi/24)*sin(1151*pi/6)=- sin(15993*pi/8):=
begin
have : -sin(pi / 3) * cos(11 * pi / 24) + sin(11 * pi / 24) * -sin(1151 * pi / 6) = -sin(pi/3)*cos(11*pi/24) - sin(11*pi/24)*sin(1151*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(1151*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11 * pi / 24) * cos(pi / 3) - sin(pi / 3) * cos(11 * pi / 24) = -sin(pi/3)*cos(11*pi/24) + sin(11*pi/24)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = sin(11*pi/24) * cos(pi/3) - sin(pi/3) * cos(11*pi/24),
{
have : sin(pi/8) = sin((11*pi/24) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = - sin(15993*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/8) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_791 : -cos(7802*pi/9) + sin(3601*pi/2)=2 * cos(-17*pi/18) * cos(-19*pi/18):=
begin
have : cos(-pi/9) = -cos(7802*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/9) (433),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3601 * pi / 2) + cos(-pi / 9) = cos(-pi/9) + sin(3601*pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(3601*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (899),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) + cos(-pi/9) = 2 * cos(-17*pi/18) * cos(-19*pi/18),
{
rw cos_add_cos,
have : cos(((-2*pi) + (-pi/9))/2) = cos(-19*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (-pi/9))/2) = cos(-17*pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_792 : -sin(4871*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(2299*pi/6) = sin(4871*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2299*pi/6) (620),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -cos(2299*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (191),
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


lemma Trigo_number_generalization_step2_793 : -1 + 2*sin(10217*pi/24)**2=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(1 - 2 * sin(10217 * pi / 24) ** 2) = -1 + 2*sin(10217*pi/24)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(10217*pi/12) = 1 - 2 * sin(10217*pi/24) ** 2,
{
have : cos(10217*pi/12) = cos(2*(10217*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(10217*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (425),
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


lemma Trigo_number_generalization_step2_794 : -sin(pi/5)*cos(11*pi/30) - sin(52241*pi/30)*cos(pi/5)=1 / 2:=
begin
have : -sin(pi / 5) * cos(11 * pi / 30) + -sin(52241 * pi / 30) * cos(pi / 5) = -sin(pi/5)*cos(11*pi/30) - sin(52241*pi/30)*cos(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/30) = -sin(52241*pi/30),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (11*pi/30) (870),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11 * pi / 30) * cos(pi / 5) - sin(pi / 5) * cos(11 * pi / 30) = -sin(pi/5)*cos(11*pi/30) + sin(11*pi/30)*cos(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(11*pi/30) * cos(pi/5) - sin(pi/5) * cos(11*pi/30),
{
have : sin(pi/6) = sin((11*pi/30) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_795 : -cos(6967*pi/6)=-sin(-2323*pi/3):=
begin
have : -sin((-2323) * pi / 3) = -sin(-2323*pi/3),
{
field_simp at *,
},
have : sin(3130*pi/3) = sin(-2323*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3130*pi/3) (134),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -cos(6967*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (580),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - sin(3130*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (521),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_796 : -1 + 2*cos(pi)**2=-cos(1975*pi/2)**2 + cos(pi)**2:=
begin
have : sin(pi) = cos(1975*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (494),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : cos(2*pi) = - sin(pi) ** 2 + cos(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_797 : sin(7*pi/8)=-sin(pi)*sin(15645*pi/8) - sin(-pi/8)*sin(2517*pi/2):=
begin
have : -sin(pi) * sin(15645 * pi / 8) + sin(-pi / 8) * -sin(2517 * pi / 2) = -sin(pi)*sin(15645*pi/8) - sin(-pi/8)*sin(2517*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -sin(2517*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (628),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * -sin(15645 * pi / 8) + sin(-pi / 8) * cos(pi) = -sin(pi)*sin(15645*pi/8) + sin(-pi/8)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = -sin(15645*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (977),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(7*pi/8) = sin(pi) * cos(-pi/8) + sin(-pi/8) * cos(pi),
{
have : sin(7*pi/8) = sin((pi) + (-pi/8)),
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


lemma Trigo_number_generalization_step2_798 : cos(8143*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(945*pi/4) = cos(8143*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (945*pi/4) (899),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(945*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (118),
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


lemma Trigo_number_generalization_step2_799 : -sin(18431*pi/24)**2 + cos(18431*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(18431*pi/12) = -sin(18431*pi/24) ** 2 + cos(18431*pi/24) ** 2,
{
have : cos(18431*pi/12) = cos(2*(18431*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = cos(18431*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/12) (768),
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


lemma Trigo_number_generalization_step2_800 : -sin(-pi/6)*cos(3287*pi/3) - sin(3287*pi/3)*cos(-pi/6)=1:=
begin
have : -(sin(3287 * pi / 3) * cos(-pi / 6) + sin(-pi / 6) * cos(3287 * pi / 3)) = -sin(-pi/6)*cos(3287*pi/3) - sin(3287*pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2191*pi/2) = sin(3287*pi/3) * cos(-pi/6) + sin(-pi/6) * cos(3287*pi/3),
{
have : sin(2191*pi/2) = sin((3287*pi/3) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(2191*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (548),
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


lemma Trigo_number_generalization_step2_801 : -cos(478*pi)**2 + sin(478*pi)**2=- cos(1748*pi):=
begin
have : -(-sin(478 * pi) ** 2 + cos(478 * pi) ** 2) = -cos(478*pi)**2 + sin(478*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(956*pi) = -sin(478*pi) ** 2 + cos(478*pi) ** 2,
{
have : cos(956*pi) = cos(2*(478*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(956*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (477),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - cos(1748*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (873),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_802 (h0 : cos(pi/24)≠ 0) (h1 : (1-tan(pi/24)**2)≠ 0) (h2 : (1-tan(1895*pi/24)**2)≠ 0) (h3 : (1-(-tan(1895*pi/24))**2)≠ 0) : -2*tan(1895*pi/24)/(1 - tan(1895*pi/24)**2)=2 - sqrt( 3 ):=
begin
have : 2 * -tan(1895 * pi / 24) / (1 - (-tan(1895 * pi / 24)) ** 2) = -2*tan(1895*pi/24)/(1 - tan(1895*pi/24)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/24) = -tan(1895*pi/24),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/24) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 * tan(pi/24) / ( 1 - tan(pi/24) ** 2 ),
{
have : tan(pi/12) = tan(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_803 : 1 - 2*cos(7517*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : -(2 * cos(7517 * pi / 12) ** 2 - 1) = 1 - 2*cos(7517*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(7517*pi/6) = 2 * cos(7517*pi/12) ** 2 - 1,
{
have : cos(7517*pi/6) = cos(2*(7517*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(7517*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (626),
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


lemma Trigo_number_generalization_step2_804 : -cos(-pi/5)*cos(14507*pi/8)=cos(75657*pi/40)/2 - sin(-13*pi/40)/2:=
begin
have : -sin((-13) * pi / 40) / 2 + cos(75657 * pi / 40) / 2 = cos(75657*pi/40)/2 - sin(-13*pi/40)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/40) = cos(75657*pi/40),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/40) (945),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -cos(14507 * pi / 8) * cos(-pi / 5) = -cos(-pi/5)*cos(14507*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -cos(14507*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (906),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) * cos(-pi/5) = - sin(-13*pi/40) / 2 + sin(-3*pi/40) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/5) + (pi/8)) = sin(-3*pi/40),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/5) - (pi/8)) = sin(-13*pi/40),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_805 (h0 : cos(pi/84)≠ 0) (h1 : cos(pi/84)≠ 0) (h2 : (2*cos(pi/84))≠ 0) : -2*sin(pi/84)*sin(13*pi/84)=-sin(pi/42)*sin(13*pi/84)/cos(pi/84):=
begin
have : (-2) * sin(pi / 84) * sin(13 * pi / 84) = -2*sin(pi/84)*sin(13*pi/84),
{
field_simp at *,
},
have : cos(pi/6) - cos(pi/7) = -2 * sin(pi/84) * sin(13*pi/84),
{
rw cos_sub_cos,
have : sin(((pi/6) + (pi/7))/2) = sin(13*pi/84),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (pi/7))/2) = sin(pi/84),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(pi/6) - cos(pi/7)) = cos(pi/6)-cos(pi/7),
{
ring,
},
have : (-2) * (sin(pi / 42) / (2 * cos(pi / 84))) * sin(13 * pi / 84) = -sin(pi/42)*sin(13*pi/84)/cos(pi/84),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/84) = sin(pi/42) / ( 2 * cos(pi/84) ),
{
have : sin(pi/42) = sin(2*(pi/84)),
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
have : cos(pi/6) - cos(pi/7) = - 2 * sin(pi/84) * sin(13*pi/84),
{
rw cos_sub_cos,
have : sin(((pi/6) + (pi/7))/2) = sin(13*pi/84),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (pi/7))/2) = sin(pi/84),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_806 (h0 : sin(pi/4)≠ 0) (h1 : (4*sin(pi/4))≠ 0) (h2 : (2*sin(pi/4))≠ 0) : sin(6793*pi/8)**2=-sin(pi/2)/(4*sin(pi/4)) + 1/2:=
begin
have : 1 / 2 - sin(pi / 2) / (2 * sin(pi / 4)) / 2 = -sin(pi/2)/(4*sin(pi/4)) + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = sin(pi/2) / ( 2 * sin(pi/4) ),
{
have : sin(pi/2) = sin(2*(pi/4)),
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
have : (-sin(6793 * pi / 8)) ** 2 = sin(6793*pi/8)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -sin(6793*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/8) (424),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) ** 2 = 1 / 2 - cos(pi/4) / 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
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


lemma Trigo_number_generalization_step2_807 (h0 : tan(10075*pi/12)≠ 0) (h1 : -tan(53*pi/12)≠ 0) (h2 : tan(53*pi/12)≠ 0) : 1/tan(53*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / -tan(53 * pi / 12) = 1/tan(53*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(10075*pi/12) = -tan(53*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (10075*pi/12) (844),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(10075 * pi / 12) = -1/tan(10075*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(10075*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (839),
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


lemma Trigo_number_generalization_step2_808 : sin(-pi/8)*sin(28255*pi/24) - cos(-pi/8)*cos(28255*pi/24)=sqrt( 3 ) / 2:=
begin
have : -(-sin(28255 * pi / 24) * sin(-pi / 8) + cos(28255 * pi / 24) * cos(-pi / 8)) = sin(-pi/8)*sin(28255*pi/24) - cos(-pi/8)*cos(28255*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7063*pi/6) = -sin(28255*pi/24) * sin(-pi/8) + cos(28255*pi/24) * cos(-pi/8),
{
have : cos(7063*pi/6) = cos((28255*pi/24) + (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -cos(7063*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (588),
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


lemma Trigo_number_generalization_step2_809 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) : 2*sin(pi/3)**2/sin(2*pi/3)=sqrt( 3 ):=
begin
have : (1 - (1 - 2 * sin(pi / 3) ** 2)) / sin(2 * pi / 3) = 2*sin(pi/3)**2/sin(2*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = 1 - 2 * sin(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( 1 - cos(2*pi/3) ) / sin(2*pi/3),
{
have : tan(pi/3) = tan((2*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_810 (h0 : cos(4875*pi/4)≠ 0) (h1 : (2*cos(4875*pi/4))≠ 0) (h2 : (2*cos(4875*pi/4)**2)≠ 0) : cos(-pi/2)=-sin(4875*pi/2)**2/(2*cos(4875*pi/4)**2) + 1:=
begin
have : 1 - 2 * (sin(4875 * pi / 2) / (2 * cos(4875 * pi / 4))) ** 2 = -sin(4875*pi/2)**2/(2*cos(4875*pi/4)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(4875*pi/4) = sin(4875*pi/2) / ( 2 * cos(4875*pi/4) ),
{
have : sin(4875*pi/2) = sin(2*(4875*pi/4)),
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
have : 1 - 2 * (-sin(4875 * pi / 4)) ** 2 = 1 - 2*sin(4875*pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) = -sin(4875*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (609),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step2_811 : -cos(1746*pi) + cos(pi/4)=cos(-pi) + cos(-pi/4):=
begin
have : 2 * (cos(-pi / 4) / 2 + cos(-pi) / 2) = cos(-pi) + cos(-pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/8) * cos(-3*pi/8) = cos(-pi/4) / 2 + cos(-pi) / 2,
{
rw cos_mul_cos,
have : cos((-5*pi/8) + (-3*pi/8)) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-5*pi/8) - (-3*pi/8)) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(cos(-5*pi/8) * cos(-3*pi/8)) = 2*cos(-5*pi/8)*cos(-3*pi/8),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-pi) = -cos(1746*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (872),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) + cos(pi/4) = 2 * cos(-5*pi/8) * cos(-3*pi/8),
{
rw cos_add_cos,
have : cos(((-pi) + (pi/4))/2) = cos(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (pi/4))/2) = cos(-5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_812 : -cos(pi/8)*cos(5425*pi/18)=-sin(pi/72)/2 + sin(101681*pi/72)/2:=
begin
have : sin(17*pi/72) = sin(101681*pi/72),
{
rw sin_eq_sin_add_int_mul_two_pi (17*pi/72) (706),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -cos(5425 * pi / 18) * cos(pi / 8) = -cos(pi/8)*cos(5425*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = -cos(5425*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (150),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) * cos(pi/8) = - sin(pi/72) / 2 + sin(17*pi/72) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/8) + (pi/9)) = sin(17*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (pi/9)) = sin(pi/72),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_813 (h0 : cos(133*pi/3)≠ 0) : -sin(133*pi/3)/cos(133*pi/3)=- tan(430*pi/3):=
begin
have : -(sin(133 * pi / 3) / cos(133 * pi / 3)) = -sin(133*pi/3)/cos(133*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(133*pi/3) = sin(133*pi/3) / cos(133*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = -tan(133*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - tan(430*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (143),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_814 : 1 - 2*cos(3553*pi/6)**2=- 1 / 2:=
begin
have : sin(pi/3) = cos(3553*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (296),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = 1 - 2 * sin(pi/3) ** 2,
{
have : cos(2*pi/3) = cos(2*(pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_815 : -sin(3589*pi/4)=-cos(4747*pi/4):=
begin
have : cos(531*pi/4) = cos(4747*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (531*pi/4) (527),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = -sin(3589*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (448),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - cos(531*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/4) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_816 : -sin(-2*pi)*sin(7649*pi/8) + cos(-17*pi/8)*cos(-2*pi)=- sin(4059*pi/8):=
begin
have : -sin(7649 * pi / 8) * sin((-2) * pi) + cos((-17) * pi / 8) * cos((-2) * pi) = -sin(-2*pi)*sin(7649*pi/8) + cos(-17*pi/8)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-17*pi/8) = -sin(7649*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-17*pi/8) (477),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-17) * pi / 8) * sin((-2) * pi) + cos((-17) * pi / 8) * cos((-2) * pi) = sin(-17*pi/8)*sin(-2*pi) + cos(-17*pi/8)*cos(-2*pi),
{
field_simp at *,
},
have : cos(-pi/8) = sin(-17*pi/8) * sin(-2*pi) + cos(-17*pi/8) * cos(-2*pi),
{
have : cos(-pi/8) = cos((-17*pi/8) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = - sin(4059*pi/8),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (253),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_817 : -cos(2503*pi/3)=- 1 / 2:=
begin
have : sin(1489*pi/6) = cos(2503*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (1489*pi/6) (541),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(1489*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (123),
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


lemma Trigo_number_generalization_step2_818 : -cos(8143*pi/6)=sqrt( 3 ) / 2:=
begin
have : cos(8131*pi/6) = cos(8143*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (8131*pi/6) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(8131*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (677),
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


lemma Trigo_number_generalization_step2_819 (h0 : tan(821*pi/2)≠ 0) (h1 : cos((821*pi)/2)≠ 0) (h2 : sin(821*pi)≠ 0) (h3 : (sin(821*pi)/(1+cos(821*pi)))≠ 0) (h4 : (1+cos(821*pi))≠ 0) : -(cos(821*pi) + 1)/sin(821*pi)=0:=
begin
have : (-1) / (sin(821 * pi) / (1 + cos(821 * pi))) = -(cos(821*pi) + 1)/sin(821*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(821*pi/2) = sin(821*pi) / ( 1 + cos(821*pi) ),
{
have : tan(821*pi/2) = tan((821*pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(821 * pi / 2) = -1/tan(821*pi/2),
{
field_simp at *,
},
have : tan(pi) = -1 / tan(821*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (409),
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


lemma Trigo_number_generalization_step2_820 : -4*cos(1690*pi/9)**3 + 3*cos(1690*pi/9)=1 / 2:=
begin
have : (-4) * cos(1690 * pi / 9) ** 3 + 3 * cos(1690 * pi / 9) = -4*cos(1690*pi/9)**3 + 3*cos(1690*pi/9),
{
field_simp at *,
},
have : sin(5*pi/18) = cos(1690*pi/9),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/18) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(5 * pi / 18) ** 3 + 3 * sin(5 * pi / 18) = -4*sin(5*pi/18)**3 + 3*sin(5*pi/18),
{
field_simp at *,
},
have : sin(5*pi/6) = -4 * sin(5*pi/18) ** 3 + 3 * sin(5*pi/18),
{
have : sin(5*pi/6) = sin(3*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_821 (h0 : sin(pi/3)≠ 0) (h1 : sin(2*pi/3)≠ 0) (h2 : (sin(2*pi/3)/(2*sin(pi/3)))≠ 0) (h3 : (2*sin(pi/3))≠ 0) (h4 : cos(11701*pi/6)≠ 0) : tan(pi/3)=2*sin(pi/3)**2/cos(11701*pi/6):=
begin
have : sin(2*pi/3) = cos(11701*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (974),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 3) / (sin(2 * pi / 3) / (2 * sin(pi / 3))) = 2*sin(pi/3)**2/sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_822 : sin(8801*pi/8)**2=1 - sin(14243*pi/8)**2:=
begin
have : cos(-pi/8) = sin(14243*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/8) (890),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-sin(8801 * pi / 8)) ** 2 = sin(8801*pi/8)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -sin(8801*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/8) (550),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) ** 2 = 1 - cos(-pi/8) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_823 (h0 : cos((1023*pi/2)/2)≠ 0) (h1 : sin(1023*pi/2)≠ 0) : -(1 - cos(1023*pi/2))/sin(1023*pi/2)=1:=
begin
have : -((1 - cos(1023 * pi / 2)) / sin(1023 * pi / 2)) = -(1 - cos(1023*pi/2))/sin(1023*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1023*pi/4) = ( 1 - cos(1023*pi/2) ) / sin(1023*pi/2),
{
have : tan(1023*pi/4) = tan((1023*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = -tan(1023*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (256),
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


lemma Trigo_number_generalization_step2_824 : sin(14537*pi/8)*cos(-pi/8) + sin(-pi/8)*cos(14537*pi/8)=- cos(3551*pi/2):=
begin
have : sin(1817*pi) = sin(14537*pi/8) * cos(-pi/8) + sin(-pi/8) * cos(14537*pi/8),
{
have : sin(1817*pi) = sin((14537*pi/8) + (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(1817*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (908),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(3551*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (887),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_825 (h0 : cos((-4*pi)/2)≠ 0) (h1 : sin(-4*pi)≠ 0) (h2 : sin((-4)*pi)≠ 0) (h3 : (sin(-pi/5)*cos(-19*pi/5)+sin(-19*pi/5)*cos(-pi/5))≠ 0) (h4 : (sin((-19)*pi/5)*cos(-pi/5)+sin(-pi/5)*cos((-19)*pi/5))≠ 0) : (1 - cos(-4*pi))/(sin(-pi/5)*cos(-19*pi/5) + sin(-19*pi/5)*cos(-pi/5))=- tan(854*pi):=
begin
have : (1 - cos((-4) * pi)) / (sin((-19) * pi / 5) * cos(-pi / 5) + sin(-pi / 5) * cos((-19) * pi / 5)) = (1 - cos(-4*pi))/(sin(-pi/5)*cos(-19*pi/5) + sin(-19*pi/5)*cos(-pi/5)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-4*pi) = sin(-19*pi/5) * cos(-pi/5) + sin(-pi/5) * cos(-19*pi/5),
{
have : sin(-4*pi) = sin((-19*pi/5) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos((-4) * pi)) / sin((-4) * pi) = (1 - cos(-4*pi))/sin(-4*pi),
{
field_simp at *,
},
have : tan(-2*pi) = ( 1 - cos(-4*pi) ) / sin(-4*pi),
{
have : tan(-2*pi) = tan((-4*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = - tan(854*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-2*pi) (852),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_826 (h0 : cos((1699*pi/3)/2)≠ 0) (h1 : sin(1699*pi/3)≠ 0) : (1 - cos(1699*pi/3))/sin(1699*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(1699*pi/6) = ( 1 - cos(1699*pi/3) ) / sin(1699*pi/3),
{
have : tan(1699*pi/6) = tan((1699*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(1699*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (283),
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


lemma Trigo_number_generalization_step2_827 : -sin(pi/5)*sin(3*pi/10) + cos(pi/5)*cos(3*pi/10)=-3*sin(1940*pi/3) + 4*sin(1940*pi/3)**3:=
begin
have : -sin(3 * pi / 10) * sin(pi / 5) + cos(3 * pi / 10) * cos(pi / 5) = -sin(pi/5)*sin(3*pi/10) + cos(pi/5)*cos(3*pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(3*pi/10) * sin(pi/5) + cos(3*pi/10) * cos(pi/5),
{
have : cos(pi/2) = cos((3*pi/10) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -((-4) * sin(1940 * pi / 3) ** 3 + 3 * sin(1940 * pi / 3)) = -3*sin(1940*pi/3) + 4*sin(1940*pi/3)**3,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1940*pi) = -4 * sin(1940*pi/3) ** 3 + 3 * sin(1940*pi/3),
{
have : sin(1940*pi) = sin(3*(1940*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(1940*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (969),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_828 : (1 - 2*sin(pi/4)**2)*sin(-pi/6) + sin(pi/2)*cos(-pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(-pi / 6) * (1 - 2 * sin(pi / 4) ** 2) + sin(pi / 2) * cos(-pi / 6) = (1 - 2*sin(pi/4)**2)*sin(-pi/6) + sin(pi/2)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/3) = sin(-pi/6) * cos(pi/2) + sin(pi/2) * cos(-pi/6),
{
have : sin(pi/3) = sin((-pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_829 : sin(20489*pi/18)=-sin(17029*pi/9)**2 + cos(pi/9)**2:=
begin
have : cos(2*pi/9) = sin(20489*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/9) (569),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(17029*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/9) (946),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/9) = - sin(pi/9) ** 2 + cos(pi/9) ** 2,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
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


lemma Trigo_number_generalization_step2_830 : sin(-pi/24)*cos(pi/8) + sin(6119*pi/8)*cos(-pi/24)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/8) = sin(6119*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/8) (382),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(-pi/24) * cos(pi/8) + sin(pi/8) * cos(-pi/24),
{
have : sin(pi/12) = sin((-pi/24) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_831 : sin(-11*pi/5)*cos(-pi/5) - (sin(-94*pi/45)*sin(pi/9) + cos(-94*pi/45)*cos(pi/9))*sin(-pi/5)=sin(922*pi):=
begin
have : sin((-11) * pi / 5) * cos(-pi / 5) - sin(-pi / 5) * (sin((-94) * pi / 45) * sin(pi / 9) + cos((-94) * pi / 45) * cos(pi / 9)) = sin(-11*pi/5)*cos(-pi/5) - (sin(-94*pi/45)*sin(pi/9) + cos(-94*pi/45)*cos(pi/9))*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-11*pi/5) = sin(-94*pi/45) * sin(pi/9) + cos(-94*pi/45) * cos(pi/9),
{
have : cos(-11*pi/5) = cos((-94*pi/45) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-11) * pi / 5) * cos(-pi / 5) - sin(-pi / 5) * cos((-11) * pi / 5) = sin(-11*pi/5)*cos(-pi/5) - sin(-pi/5)*cos(-11*pi/5),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-11*pi/5) * cos(-pi/5) - sin(-pi/5) * cos(-11*pi/5),
{
have : sin(-2*pi) = sin((-11*pi/5) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(922*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (462),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_832 : -sin(4045*pi/6)=- 1 / 2:=
begin
have : sin(1573*pi/6) = sin(4045*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (1573*pi/6) (206),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(1573*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (130),
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


lemma Trigo_number_generalization_step2_833 : tan(12985*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(9901*pi/12) = tan(12985*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (9901*pi/12) (257),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = tan(9901*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (825),
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


lemma Trigo_number_generalization_step2_834 (h0 : tan(3997*pi/4)≠ 0) (h1 : tan(6117*pi/4)≠ 0) : 1/tan(6117*pi/4)=tan(1813*pi/4):=
begin
have : tan(3997*pi/4) = tan(6117*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (3997*pi/4) (530),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1 / tan(3997*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = tan(1813*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (pi/4) (453),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_835 : -4*sin(53*pi/18)**3 + 3*sin(53*pi/18)=sin(11141*pi/6):=
begin
have : (-4) * sin(53 * pi / 18) ** 3 + 3 * sin(53 * pi / 18) = -4*sin(53*pi/18)**3 + 3*sin(53*pi/18),
{
field_simp at *,
},
have : sin(pi/18) = sin(53*pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/18) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/6) = sin(11141*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (928),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_836 : -cos(12467*pi/8)=sin(-pi/8)*sin(3845*pi/2) + cos(-pi/2)*cos(-pi/8):=
begin
have : -sin(-pi / 8) * -sin(3845 * pi / 2) + cos(-pi / 8) * cos(-pi / 2) = sin(-pi/8)*sin(3845*pi/2) + cos(-pi/2)*cos(-pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -sin(3845*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (961),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/8) = -cos(12467*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-5*pi/8) (779),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/8) = - sin(-pi/8) * sin(-pi/2) + cos(-pi/8) * cos(-pi/2),
{
have : cos(-5*pi/8) = cos((-pi/8) + (-pi/2)),
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


lemma Trigo_number_generalization_step2_837 : sin(-pi)*sin(6333*pi/14)=sin(-pi)*cos(pi/7):=
begin
have : 1 / 2 * (2 * sin(-pi) * cos(pi / 7)) = sin(-pi)*cos(pi/7),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-6*pi/7) - sin(8*pi/7) = 2 * sin(-pi) * cos(pi/7),
{
rw sin_sub_sin,
have : cos(((-6*pi/7) + (8*pi/7))/2) = cos(pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-6*pi/7) - (8*pi/7))/2) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 1/2*(sin(-6*pi/7) - sin(8*pi/7)) = -sin(8*pi/7)/2+sin(-6*pi/7)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : cos(pi/7) = sin(6333*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/7) (226),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * cos(pi/7) = - sin(8*pi/7) / 2 + sin(-6*pi/7) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/7) + (-pi)) = sin(-6*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/7) - (-pi)) = sin(8*pi/7),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_838 : cos(pi/3) + sin(4273*pi/6)=2 * cos(pi/3) * cos(0):=
begin
have : - -sin(4273 * pi / 6) + cos(pi / 3) = cos(pi/3) + sin(4273*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7511*pi/6) = -sin(4273*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (7511*pi/6) (982),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 3) + -sin(7511 * pi / 6) = -sin(7511*pi/6) + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(7511*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (625),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) + cos(-pi/3) = 2 * cos(pi/3) * cos(0),
{
rw cos_add_cos,
have : cos(((pi/3) + (-pi/3))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (-pi/3))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_839 (h0 : tan(1491*pi/2)≠ 0) (h1 : cos((1491*pi)/2)≠ 0) (h2 : (sin(1491*pi)/(1+cos(1491*pi)))≠ 0) (h3 : sin(1491*pi)≠ 0) (h4 : (1+cos(1491*pi))≠ 0) : (cos(1491*pi) + 1)/sin(1491*pi)=0:=
begin
have : 1 / (sin(1491 * pi) / (1 + cos(1491 * pi))) = (cos(1491*pi) + 1)/sin(1491*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(1491*pi/2) = sin(1491*pi) / ( 1 + cos(1491*pi) ),
{
have : tan(1491*pi/2) = tan((1491*pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(1491*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (746),
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


lemma Trigo_number_generalization_step2_840 (h0 : sin(397*pi/8)≠ 0) (h1 : (2*sin(397*pi/8))≠ 0) : sin(6791*pi/8)=sin(397*pi/4)/(2*sin(397*pi/8)):=
begin
have : sin(pi/8) = sin(6791*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/8) (424),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(397*pi/8) = sin(397*pi/4) / ( 2 * sin(397*pi/8) ),
{
have : sin(397*pi/4) = sin(2*(397*pi/8)),
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
have : sin(pi/8) = cos(397*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_841 : 1 - 2*cos(369*pi)**2=4 * cos(-pi/3) ** 3 - 3 * cos(-pi/3):=
begin
have : sin(-pi/2) = cos(369*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (184),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step2_842 (h0 : tan(5449*pi/6)≠ 0) : -1/tan(5449*pi/6)=- sqrt( 3 ):=
begin
have : -(1 / tan(5449 * pi / 6)) = -1/tan(5449*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(166*pi/3) = 1 / tan(5449*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (166*pi/3) (963),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(166*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (56),
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


lemma Trigo_number_generalization_step2_843 : -3*sin(5636*pi/9) + 4*sin(5636*pi/9)**3=- sin(5845*pi/3):=
begin
have : -((-4) * sin(5636 * pi / 9) ** 3 + 3 * sin(5636 * pi / 9)) = -3*sin(5636*pi/9) + 4*sin(5636*pi/9)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5636*pi/3) = -4 * sin(5636*pi/9) ** 3 + 3 * sin(5636*pi/9),
{
have : sin(5636*pi/3) = sin(3*(5636*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(5636*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (939),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(5845*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (974),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_844 (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) (h2 : cos((-4*pi)/2)≠ 0) (h3 : sin(-4*pi)≠ 0) (h4 : sin((-4)*pi)≠ 0) : cos(2939*pi/2)/cos(-2*pi)=(1 - cos(-4*pi))/sin(-4*pi):=
begin
have : (1 - cos((-4) * pi)) / sin((-4) * pi) = (1 - cos(-4*pi))/sin(-4*pi),
{
field_simp at *,
},
have : tan(-2*pi) = ( 1 - cos(-4*pi) ) / sin(-4*pi),
{
have : tan(-2*pi) = tan((-4*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : cos(2939 * pi / 2) / cos((-2) * pi) = cos(2939*pi/2)/cos(-2*pi),
{
field_simp at *,
},
have : sin(-2*pi) = cos(2939*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (735),
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


lemma Trigo_number_generalization_step2_845 : 2*sin(7721*pi/12)*cos(7721*pi/12) + cos(2*pi)=2 * cos(5*pi/6) * cos(7*pi/6):=
begin
have : sin(7721*pi/6) = 2 * sin(7721*pi/12) * cos(7721*pi/12),
{
have : sin(7721*pi/6) = sin(2*(7721*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(2 * pi) + sin(7721 * pi / 6) = sin(7721*pi/6) + cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(7721*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (643),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) + cos(pi/3) = 2 * cos(5*pi/6) * cos(7*pi/6),
{
rw cos_add_cos,
have : cos(((2*pi) + (pi/3))/2) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((2*pi) - (pi/3))/2) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_846 : sin(13873*pi/10)*cos(9496*pi/9)=cos(-14*pi/45) / 2 + cos(-4*pi/45) / 2:=
begin
have : - -sin(13873 * pi / 10) * cos(9496 * pi / 9) = sin(13873*pi/10)*cos(9496*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = -sin(13873*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (693),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi / 5) * -cos(9496 * pi / 9) = -cos(-pi/5)*cos(9496*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -cos(9496*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/9) (527),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) * cos(pi/9) = cos(-14*pi/45) / 2 + cos(-4*pi/45) / 2,
{
rw cos_mul_cos,
have : cos((-pi/5) + (pi/9)) = cos(-4*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (pi/9)) = cos(-14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_847 (h0 : cos(-13*pi/40)≠ 0) (h1 : (2*cos(-13*pi/40))≠ 0) (h2 : (2*cos((-13)*pi/40))≠ 0) : sin(-13*pi/20)*sin(-pi/8)/(2*cos(-13*pi/40)) + cos(-13*pi/40)*cos(-pi/8)=- sin(13297*pi/10):=
begin
have : sin((-13) * pi / 20) / (2 * cos((-13) * pi / 40)) * sin(-pi / 8) + cos((-13) * pi / 40) * cos(-pi / 8) = sin(-13*pi/20)*sin(-pi/8)/(2*cos(-13*pi/40)) + cos(-13*pi/40)*cos(-pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-13*pi/40) = sin(-13*pi/20) / ( 2 * cos(-13*pi/40) ),
{
have : sin(-13*pi/20) = sin(2*(-13*pi/40)),
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
have : sin((-13) * pi / 40) * sin(-pi / 8) + cos((-13) * pi / 40) * cos(-pi / 8) = sin(-13*pi/40)*sin(-pi/8) + cos(-13*pi/40)*cos(-pi/8),
{
field_simp at *,
},
have : cos(-pi/5) = sin(-13*pi/40) * sin(-pi/8) + cos(-13*pi/40) * cos(-pi/8),
{
have : cos(-pi/5) = cos((-13*pi/40) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = - sin(13297*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (664),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_848 (h0 : cos(3467*pi/12)≠ 0) (h1 : (1-tan(3467*pi/12)**2)≠ 0) : -2*tan(3467*pi/12)/(1 - tan(3467*pi/12)**2)=sqrt( 3 ) / 3:=
begin
have : -(2 * tan(3467 * pi / 12) / (1 - tan(3467 * pi / 12) ** 2)) = -2*tan(3467*pi/12)/(1 - tan(3467*pi/12)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3467*pi/6) = 2 * tan(3467*pi/12) / ( 1 - tan(3467*pi/12) ** 2 ),
{
have : tan(3467*pi/6) = tan(2*(3467*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(3467*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (578),
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


lemma Trigo_number_generalization_step2_849 (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) (h2 : (2*sin(pi/6)**3)≠ 0) : -3*sin(pi/3)/(2*sin(pi/6)) + sin(pi/3)**3/(2*sin(pi/6)**3)=cos(3347*pi/2):=
begin
have : (-3) * (sin(pi / 3) / (2 * sin(pi / 6))) + 4 * (sin(pi / 3) / (2 * sin(pi / 6))) ** 3 = -3*sin(pi/3)/(2*sin(pi/6)) + sin(pi/3)**3/(2*sin(pi/6)**3),
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
have : 4 * cos(pi / 6) ** 3 - 3 * cos(pi / 6) = -3*cos(pi/6) + 4*cos(pi/6)**3,
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
have : cos(pi/2) = cos(3347*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (837),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_850 (h0 : sin(26045*pi/14)≠ 0) (h1 : (2*sin(26045*pi/14))≠ 0) : -cos(4321*pi/14)=sin(26045*pi/7)/(2*sin(26045*pi/14)):=
begin
have : sin(pi/7) = -cos(4321*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/7) (154),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(26045*pi/14) = sin(26045*pi/7) / ( 2 * sin(26045*pi/14) ),
{
have : sin(26045*pi/7) = sin(2*(26045*pi/14)),
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
have : sin(pi/7) = cos(26045*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/7) (930),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_851 : 2*sin(9*pi/8)*cos(9*pi/8)=sin(2*pi)*cos(pi/4) + (1 - 2*sin(pi)**2)*sin(pi/4):=
begin
have : sin(9*pi/4) = 2 * sin(9*pi/8) * cos(9*pi/8),
{
have : sin(9*pi/4) = sin(2*(9*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) * cos(pi / 4) + sin(pi / 4) * (1 - 2 * sin(pi) ** 2) = sin(2*pi)*cos(pi/4) + (1 - 2*sin(pi)**2)*sin(pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = 1 - 2 * sin(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(9*pi/4) = sin(2*pi) * cos(pi/4) + sin(pi/4) * cos(2*pi),
{
have : sin(9*pi/4) = sin((2*pi) + (pi/4)),
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


lemma Trigo_number_generalization_step2_852 : sin(-3*pi/4)=sin(-pi/2)*cos(-pi/4) + (sin(1404*pi)*cos(-2*pi) - sin(-2*pi)*sin(3*pi/2))*sin(-pi/4):=
begin
have : sin(-pi / 2) * cos(-pi / 4) + (cos((-2) * pi) * sin(1404 * pi) - sin((-2) * pi) * sin(3 * pi / 2)) * sin(-pi / 4) = sin(-pi/2)*cos(-pi/4) + (sin(1404*pi)*cos(-2*pi) - sin(-2*pi)*sin(3*pi/2))*sin(-pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/2) = sin(1404*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/2) (701),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 4) * (-sin(3 * pi / 2) * sin((-2) * pi) + cos(3 * pi / 2) * cos((-2) * pi)) + sin(-pi / 2) * cos(-pi / 4) = sin(-pi/2)*cos(-pi/4) + (cos(-2*pi)*cos(3*pi/2) - sin(-2*pi)*sin(3*pi/2))*sin(-pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -sin(3*pi/2) * sin(-2*pi) + cos(3*pi/2) * cos(-2*pi),
{
have : cos(-pi/2) = cos((3*pi/2) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/4) = sin(-pi/4) * cos(-pi/2) + sin(-pi/2) * cos(-pi/4),
{
have : sin(-3*pi/4) = sin((-pi/4) + (-pi/2)),
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


lemma Trigo_number_generalization_step2_853 : -cos(9211*pi/6)=-cos(13109*pi/6):=
begin
have : sin(3676*pi/3) = cos(13109*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3676*pi/3) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = -cos(9211*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (767),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(3676*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (612),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_854 : sin(69373*pi/90)=sin(-pi/9)*sin(pi/5) + cos(14*pi/45)/2 + cos(4*pi/45)/2:=
begin
have : cos(14*pi/45) = sin(69373*pi/90),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (14*pi/45) (385),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 5) * sin(-pi / 9) + (cos(14 * pi / 45) / 2 + cos(4 * pi / 45) / 2) = sin(-pi/9)*sin(pi/5) + cos(14*pi/45)/2 + cos(4*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) * cos(-pi/9) = cos(14*pi/45) / 2 + cos(4*pi/45) / 2,
{
rw cos_mul_cos,
have : cos((pi/5) + (-pi/9)) = cos(4*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/5) - (-pi/9)) = cos(14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (cos(pi/5) * cos(-pi/9)) = cos(pi/5)*cos(-pi/9),
{
ring,
},
have : cos(14*pi/45) = sin(pi/5) * sin(-pi/9) + cos(pi/5) * cos(-pi/9),
{
have : cos(14*pi/45) = cos((pi/5) - (-pi/9)),
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


lemma Trigo_number_generalization_step2_855 (h0 : tan(2077*pi/6)≠ 0) (h1 : cos(2077*pi/12)≠ 0) (h2 : (2*tan(2077*pi/12))≠ 0) (h3 : (2*tan(2077*pi/12)/(1-tan(2077*pi/12)**2))≠ 0) (h4 : (1-tan(2077*pi/12)**2)≠ 0) : -(1 - tan(2077*pi/12)**2)/(2*tan(2077*pi/12))=- sqrt( 3 ):=
begin
have : (-1) / (2 * tan(2077 * pi / 12) / (1 - tan(2077 * pi / 12) ** 2)) = -(1 - tan(2077*pi/12)**2)/(2*tan(2077*pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2077*pi/6) = 2 * tan(2077*pi/12) / ( 1 - tan(2077*pi/12) ** 2 ),
{
have : tan(2077*pi/6) = tan(2*(2077*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(2077 * pi / 6) = -1/tan(2077*pi/6),
{
field_simp at *,
},
have : tan(2*pi/3) = -1 / tan(2077*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi/3) (345),
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


lemma Trigo_number_generalization_step2_856 (h0 : cos(pi)≠ 0) : -sin(933*pi)/cos(pi)=- 1 / tan(1105*pi/2):=
begin
have : sin(pi) = -sin(933*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (467),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(1105*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (551),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_857 : 1 - 2*sin(1649*pi/8)**2=sqrt( 2 ) / 2:=
begin
have : cos(1649*pi/4) = 1 - 2 * sin(1649*pi/8) ** 2,
{
have : cos(1649*pi/4) = cos(2*(1649*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = cos(1649*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (205),
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


lemma Trigo_number_generalization_step2_858 : -cos(pi/5)*cos(28643*pi/15) - sin(pi/5)*cos(31*pi/30)=1 / 2:=
begin
have : -cos(28643 * pi / 15) * cos(pi / 5) - sin(pi / 5) * cos(31 * pi / 30) = -cos(pi/5)*cos(28643*pi/15) - sin(pi/5)*cos(31*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(31*pi/30) = -cos(28643*pi/15),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (31*pi/30) (954),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(31*pi/30) * cos(pi/5) - sin(pi/5) * cos(31*pi/30),
{
have : sin(5*pi/6) = sin((31*pi/30) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_859 : -1 + 2*sin(3587*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -1 + 2 * (-sin(3587 * pi / 24)) ** 2 = -1 + 2*sin(3587*pi/24)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -sin(3587*pi/24),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/24) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 24) ** 2 - 1 = -1 + 2*cos(pi/24)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = 2 * cos(pi/24) ** 2 - 1,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_860 : 4*sin(71173*pi/36)**3 - 3*sin(71173*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-4) * (-sin(71173 * pi / 36)) ** 3 + 3 * -sin(71173 * pi / 36) = 4*sin(71173*pi/36)**3 - 3*sin(71173*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) = -sin(71173*pi/36),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/36) (988),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36) = -4*sin(pi/36)**3 + 3*sin(pi/36),
{
field_simp at *,
},
have : sin(pi/12) = -4 * sin(pi/36) ** 3 + 3 * sin(pi/36),
{
have : sin(pi/12) = sin(3*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_861 : sin(-pi/8) * sin(pi/7)=-cos(pi/56)/2 + sin(15835*pi/56)/2:=
begin
have : -cos(pi / 56) / 2 - -sin(15835 * pi / 56) / 2 = -cos(pi/56)/2 + sin(15835*pi/56)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(95801*pi/56) = -sin(15835*pi/56),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (95801*pi/56) (996),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -cos(95801 * pi / 56) / 2 - cos(pi / 56) / 2 = -cos(pi/56)/2 - cos(95801*pi/56)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-15*pi/56) = -cos(95801*pi/56),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-15*pi/56) (855),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) * sin(pi/7) = cos(-15*pi/56) / 2 - cos(pi/56) / 2,
{
rw sin_mul_sin,
have : cos((-pi/8) + (pi/7)) = cos(pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/8) - (pi/7)) = cos(-15*pi/56),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_862 : -2*sin(641*pi/7)*cos(641*pi/7)=- sin(4297*pi/7):=
begin
have : -(2 * sin(641 * pi / 7) * cos(641 * pi / 7)) = -2*sin(641*pi/7)*cos(641*pi/7),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1282*pi/7) = 2 * sin(641*pi/7) * cos(641*pi/7),
{
have : sin(1282*pi/7) = sin(2*(641*pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = -sin(1282*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/7) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = - sin(4297*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/7) (307),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_863 : sin(7*pi/6)*cos(-pi/2) + cos(7*pi/6)*cos(141*pi)=sqrt( 3 ) / 2:=
begin
have : sin(7 * pi / 6) * cos(-pi / 2) + cos(141 * pi) * cos(7 * pi / 6) = sin(7*pi/6)*cos(-pi/2) + cos(7*pi/6)*cos(141*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(141*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(7*pi/6) * cos(-pi/2) + sin(-pi/2) * cos(7*pi/6),
{
have : sin(2*pi/3) = sin((7*pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_864 : sin(395*pi/2)=- 1:=
begin
have : cos(1733*pi) = sin(395*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (1733*pi) (965),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(1733*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (867),
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


lemma Trigo_number_generalization_step2_865 : -cos(17453*pi/5)=1 - 2 * sin(-pi/5) ** 2:=
begin
have : cos(8418*pi/5) = -cos(17453*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (8418*pi/5) (903),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = cos(8418*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi/5) (842),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/5) = 1 - 2 * sin(-pi/5) ** 2,
{
have : cos(-2*pi/5) = cos(2*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_866 : sin(-11733*pi/10)*sin(-pi/3)=- sin(8*pi/15) / 2 + sin(-2*pi/15) / 2:=
begin
have : -sin(-pi / 3) * -sin((-11733) * pi / 10) = sin(-11733*pi/10)*sin(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(15933*pi/10) = -sin(-11733*pi/10),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (15933*pi/10) (210),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 3) * -sin(15933 * pi / 10) = -sin(-pi/3)*sin(15933*pi/10),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -sin(15933*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (796),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi/5) = - sin(8*pi/15) / 2 + sin(-2*pi/15) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/5) + (-pi/3)) = sin(-2*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (-pi/3)) = sin(8*pi/15),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_867 (h0 : cos(pi)≠ 0) : -cos(2265*pi/2)/cos(pi)=0:=
begin
have : sin(pi) = -cos(2265*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (566),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_868 : 1/2 + cos(-4*pi)/2=1 - cos(129*pi/2)**2:=
begin
have : cos((-4) * pi) / 2 + 1 / 2 = 1/2 + cos(-4*pi)/2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : 1 - (-cos(129 * pi / 2)) ** 2 = 1 - cos(129*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = -cos(129*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (33),
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


lemma Trigo_number_generalization_step2_869 : sin(-3367*pi/2)=1:=
begin
have : sin((-3367) * pi / 2) = sin(-3367*pi/2),
{
field_simp at *,
},
have : cos(1996*pi) = sin(-3367*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (1996*pi) (156),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(1996*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (998),
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


lemma Trigo_number_generalization_step2_870 (h0 : cos(3415*pi/12)≠ 0) (h1 : (1-tan(3415*pi/12)**2)≠ 0) : 2*tan(3415*pi/12)/(1 - tan(3415*pi/12)**2)=sqrt( 3 ) / 3:=
begin
have : tan(3415*pi/6) = 2 * tan(3415*pi/12) / ( 1 - tan(3415*pi/12) ** 2 ),
{
have : tan(3415*pi/6) = tan(2*(3415*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(3415*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (569),
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


lemma Trigo_number_generalization_step2_871 (h0 : cos(pi/2)≠ 0) (h1 : (1-tan(pi/2)**2)≠ 0) (h2 : (1-tan(337*pi/2)**2)≠ 0) : 2*tan(337*pi/2)/(1 - tan(337*pi/2)**2)=- 1 / tan(269*pi/2):=
begin
have : tan(pi/2) = tan(337*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (168),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 2 * tan(pi/2) / ( 1 - tan(pi/2) ** 2 ),
{
have : tan(pi) = tan(2*(pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(269*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (133),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_872 : 3*sin(-pi/24) - 4*sin(-pi/24)**3=1 - 2*cos(5011*pi/16)**2:=
begin
have : -(2 * cos(5011 * pi / 16) ** 2 - 1) = 1 - 2*cos(5011*pi/16)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(5011*pi/8) = 2 * cos(5011*pi/16) ** 2 - 1,
{
have : cos(5011*pi/8) = cos(2*(5011*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : (-4) * sin(-pi / 24) ** 3 + 3 * sin(-pi / 24) = 3*sin(-pi/24) - 4*sin(-pi/24)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = -4 * sin(-pi/24) ** 3 + 3 * sin(-pi/24),
{
have : sin(-pi/8) = sin(3*(-pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = - cos(5011*pi/8),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/8) (313),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_873 (h0 : cos(9*pi/14)≠ 0) (h1 : cos(pi/7)≠ 0) (h2 : (1+tan(9*pi/14)*tan(pi/7))≠ 0) (h3 : (tan(pi/7)*tan(9*pi/14)+1)≠ 0) (h4 : cos((9*pi/7)/2)≠ 0) (h5 : ((1-cos(9*pi/7))*tan(pi/7)/sin(9*pi/7)+1)≠ 0) (h6 : sin(9*pi/7)≠ 0) (h7 : (tan(pi/7)*((1-cos(9*pi/7))/sin(9*pi/7))+1)≠ 0) : ((1 - cos(9*pi/7))/sin(9*pi/7) - tan(pi/7))/((1 - cos(9*pi/7))*tan(pi/7)/sin(9*pi/7) + 1)=- 1 / tan(791*pi):=
begin
have : ((1 - cos(9 * pi / 7)) / sin(9 * pi / 7) - tan(pi / 7)) / (tan(pi / 7) * ((1 - cos(9 * pi / 7)) / sin(9 * pi / 7)) + 1) = ((1 - cos(9*pi/7))/sin(9*pi/7) - tan(pi/7))/((1 - cos(9*pi/7))*tan(pi/7)/sin(9*pi/7) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(9*pi/14) = ( 1 - cos(9*pi/7) ) / sin(9*pi/7),
{
have : tan(9*pi/14) = tan((9*pi/7)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(9 * pi / 14) - tan(pi / 7)) / (1 + tan(9 * pi / 14) * tan(pi / 7)) = (tan(9*pi/14) - tan(pi/7))/(tan(pi/7)*tan(9*pi/14) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = ( tan(9*pi/14) - tan(pi/7) ) / ( 1 + tan(9*pi/14) * tan(pi/7) ),
{
have : tan(pi/2) = tan((9*pi/14) - (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - 1 / tan(791*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (790),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_874 : -4*cos(2794*pi/9)**3 + 3*cos(2794*pi/9)=1 / 2:=
begin
have : (-4) * cos(2794 * pi / 9) ** 3 + 3 * cos(2794 * pi / 9) = -4*cos(2794*pi/9)**3 + 3*cos(2794*pi/9),
{
field_simp at *,
},
have : sin(pi/18) = cos(2794*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (155),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_875 (h0 : tan(25409*pi/18)≠ 0) : -1/tan(25409*pi/18)=1 / tan(8701*pi/18):=
begin
have : (-1) / tan(25409 * pi / 18) = -1/tan(25409*pi/18),
{
field_simp at *,
},
have : tan(8686*pi/9) = -1 / tan(25409*pi/18),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (8686*pi/9) (446),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = tan(8686*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (965),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 1 / tan(8701*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/9) (483),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_876 : sin(-pi/3)*sin(1526*pi) + cos(-pi/3)*cos(1526*pi)=1 / 2:=
begin
have : sin(1526 * pi) * sin(-pi / 3) + cos(1526 * pi) * cos(-pi / 3) = sin(-pi/3)*sin(1526*pi) + cos(-pi/3)*cos(1526*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4579*pi/3) = sin(1526*pi) * sin(-pi/3) + cos(1526*pi) * cos(-pi/3),
{
have : cos(4579*pi/3) = cos((1526*pi) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(4579*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (763),
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


lemma Trigo_number_generalization_step2_877 : -sin(327*pi/2)=-sin(1163*pi/2):=
begin
have : sin(pi/2) = -sin(327*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(367*pi) = sin(1163*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (367*pi) (107),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = - cos(367*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (183),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_878 (h0 : cos((-pi/4)/2)≠ 0) (h1 : sin(-pi/4)≠ 0) (h2 : -sin(5579*pi/4)≠ 0) (h3 : sin(5579*pi/4)≠ 0) : -(1 - cos(-pi/4))/sin(5579*pi/4)=- 1 / tan(4659*pi/8):=
begin
have : (1 - cos(-pi / 4)) / -sin(5579 * pi / 4) = -(1 - cos(-pi/4))/sin(5579*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -sin(5579*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (697),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = ( 1 - cos(-pi/4) ) / sin(-pi/4),
{
have : tan(-pi/8) = tan((-pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - 1 / tan(4659*pi/8),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/8) (582),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_879 (h0 : cos(-5*pi/84)≠ 0) (h1 : (2*cos((-5)*pi/84))≠ 0) (h2 : (2*cos(-5*pi/84))≠ 0) : sin(-5*pi/42)*cos(pi/7)/(2*cos(-5*pi/84)) + sin(pi/7)*cos(-5*pi/84)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin((-5) * pi / 42) / (2 * cos((-5) * pi / 84)) * cos(pi / 7) + sin(pi / 7) * cos((-5) * pi / 84) = sin(-5*pi/42)*cos(pi/7)/(2*cos(-5*pi/84)) + sin(pi/7)*cos(-5*pi/84),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/84) = sin(-5*pi/42) / ( 2 * cos(-5*pi/84) ),
{
have : sin(-5*pi/42) = sin(2*(-5*pi/84)),
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
have : sin((-5) * pi / 84) * cos(pi / 7) + sin(pi / 7) * cos((-5) * pi / 84) = sin(-5*pi/84)*cos(pi/7) + sin(pi/7)*cos(-5*pi/84),
{
field_simp at *,
},
have : sin(pi/12) = sin(-5*pi/84) * cos(pi/7) + sin(pi/7) * cos(-5*pi/84),
{
have : sin(pi/12) = sin((-5*pi/84) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_880 : (sin(-7*pi/12)*cos(pi/3) + (-1 + 2*cos(-7*pi/24)**2)*sin(pi/3))**2 + cos(-pi/4)**2=1:=
begin
have : (sin((-7) * pi / 12) * cos(pi / 3) + sin(pi / 3) * (2 * cos((-7) * pi / 24) ** 2 - 1)) ** 2 + cos(-pi / 4) ** 2 = (sin(-7*pi/12)*cos(pi/3) + (-1 + 2*cos(-7*pi/24)**2)*sin(pi/3))**2 + cos(-pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/12) = 2 * cos(-7*pi/24) ** 2 - 1,
{
have : cos(-7*pi/12) = cos(2*(-7*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : (sin((-7) * pi / 12) * cos(pi / 3) + sin(pi / 3) * cos((-7) * pi / 12)) ** 2 + cos(-pi / 4) ** 2 = (sin(-7*pi/12)*cos(pi/3) + sin(pi/3)*cos(-7*pi/12))**2 + cos(-pi/4)**2,
{
field_simp at *,
},
have : sin(-pi/4) = sin(-7*pi/12) * cos(pi/3) + sin(pi/3) * cos(-7*pi/12),
{
have : sin(-pi/4) = sin((-7*pi/12) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) ** 2 + cos(-pi/4) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_881 : -sin(581*pi/2)=sin(1663*pi/2):=
begin
have : cos(pi) = -sin(581*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (145),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(1663 * pi / 2) = sin(1663*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1253*pi/2) = -sin(1663*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1253*pi/2) (102),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = - sin(1253*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (312),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_882 : -cos(3019*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(1633*pi/4) = -cos(3019*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (1633*pi/4) (581),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(1633*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (204),
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


lemma Trigo_number_generalization_step2_883 : -sin(3*pi/8)**2 + cos(4723*pi/8)**2=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/8) = cos(4723*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/8) (295),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(3*pi/8) ** 2 + cos(3*pi/8) ** 2,
{
have : cos(3*pi/4) = cos(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_884 : -sin(31323*pi/35)=-sin(pi/5)*cos(pi/7) + (-3*cos(pi/15) + 4*cos(pi/15)**3)*sin(pi/7):=
begin
have : sin(-2*pi/35) = -sin(31323*pi/35),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/35) (447),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 7) * (4 * cos(pi / 15) ** 3 - 3 * cos(pi / 15)) - sin(pi / 5) * cos(pi / 7) = -sin(pi/5)*cos(pi/7) + (-3*cos(pi/15) + 4*cos(pi/15)**3)*sin(pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = 4 * cos(pi/15) ** 3 - 3 * cos(pi/15),
{
have : cos(pi/5) = cos(3*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/35) = sin(pi/7) * cos(pi/5) - sin(pi/5) * cos(pi/7),
{
have : sin(-2*pi/35) = sin((pi/7) - (pi/5)),
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


lemma Trigo_number_generalization_step2_885 : cos(84292*pi/63)=-(sin(-12*pi/35)*cos(pi/5) + sin(pi/5)*cos(-12*pi/35))*sin(pi/9) + cos(-pi/7)*cos(pi/9):=
begin
have : -sin(pi / 9) * (sin((-12) * pi / 35) * cos(pi / 5) + sin(pi / 5) * cos((-12) * pi / 35)) + cos(pi / 9) * cos(-pi / 7) = -(sin(-12*pi/35)*cos(pi/5) + sin(pi/5)*cos(-12*pi/35))*sin(pi/9) + cos(-pi/7)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) = sin(-12*pi/35) * cos(pi/5) + sin(pi/5) * cos(-12*pi/35),
{
have : sin(-pi/7) = sin((-12*pi/35) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/63) = cos(84292*pi/63),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi/63) (669),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/63) = - sin(pi/9) * sin(-pi/7) + cos(pi/9) * cos(-pi/7),
{
have : cos(-2*pi/63) = cos((pi/9) + (-pi/7)),
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


lemma Trigo_number_generalization_step2_886 : sin(-pi/5) ** 2=1 - (-3*sin(58637*pi/30) + 4*sin(58637*pi/30)**3)**2:=
begin
have : 1 - ((-3) * sin(58637 * pi / 30) + 4 * sin(58637 * pi / 30) ** 3) ** 2 = 1 - (-3*sin(58637*pi/30) + 4*sin(58637*pi/30)**3)**2,
{
field_simp at *,
},
have : cos(-pi/15) = sin(58637*pi/30),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/15) (977),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - (4 * cos(-pi / 15) ** 3 - 3 * cos(-pi / 15)) ** 2 = 1 - (-3*cos(-pi/15) + 4*cos(-pi/15)**3)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) = 4 * cos(-pi/15) ** 3 - 3 * cos(-pi/15),
{
have : cos(-pi/5) = cos(3*(-pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/5) ** 2 = 1 - cos(-pi/5) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step2_887 (h0 : cos(pi)≠ 0) (h1 : cos(941*pi)≠ 0) : sin(pi)/cos(941*pi)=0:=
begin
have : cos(pi) = cos(941*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (470),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_888 (h0 : sin(-3*pi/2)≠ 0) (h1 : (2*sin((-3)*pi/2))≠ 0) (h2 : (2*sin(-3*pi/2))≠ 0) : (sin(-3*pi)*sin(pi/2)/(2*sin(-3*pi/2)) + sin(-3*pi/2)*cos(pi/2))*sin(-pi/4)=cos(-3*pi/4) / 2 - cos(-5*pi/4) / 2:=
begin
have : (sin(pi / 2) * (sin((-3) * pi) / (2 * sin((-3) * pi / 2))) + sin((-3) * pi / 2) * cos(pi / 2)) * sin(-pi / 4) = (sin(-3*pi)*sin(pi/2)/(2*sin(-3*pi/2)) + sin(-3*pi/2)*cos(pi/2))*sin(-pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = sin(-3*pi) / ( 2 * sin(-3*pi/2) ),
{
have : sin(-3*pi) = sin(2*(-3*pi/2)),
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
have : (sin((-3) * pi / 2) * cos(pi / 2) + sin(pi / 2) * cos((-3) * pi / 2)) * sin(-pi / 4) = (sin(pi/2)*cos(-3*pi/2) + sin(-3*pi/2)*cos(pi/2))*sin(-pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(-3*pi/2) * cos(pi/2) + sin(pi/2) * cos(-3*pi/2),
{
have : sin(-pi) = sin((-3*pi/2) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) * sin(-pi/4) = cos(-3*pi/4) / 2 - cos(-5*pi/4) / 2,
{
rw sin_mul_sin,
have : cos((-pi) + (-pi/4)) = cos(-5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-pi/4)) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_889 : -cos(17903*pi/9)=-(-4*sin(pi/9)**3 + 3*sin(pi/9))*sin(-pi/9) + cos(-pi/9)*cos(pi/3):=
begin
have : -((-4) * sin(pi / 9) ** 3 + 3 * sin(pi / 9)) * sin(-pi / 9) + cos(pi / 3) * cos(-pi / 9) = -(-4*sin(pi/9)**3 + 3*sin(pi/9))*sin(-pi/9) + cos(-pi/9)*cos(pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = -4 * sin(pi/9) ** 3 + 3 * sin(pi/9),
{
have : sin(pi/3) = sin(3*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/9) = -cos(17903*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi/9) (994),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = - sin(pi/3) * sin(-pi/9) + cos(pi/3) * cos(-pi/9),
{
have : cos(2*pi/9) = cos((pi/3) + (-pi/9)),
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


lemma Trigo_number_generalization_step2_890 (h0 : cos((pi/6)/2)≠ 0) (h1 : sin(pi/6)≠ 0) (h2 : sin(pi/6)≠ 0) (h3 : (2*sin(pi/6))≠ 0) : (-sin(pi/3)/(2*sin(pi/6)) + 1)/sin(pi/6)=2 - sqrt( 3 ):=
begin
have : (1 - sin(pi / 3) / (2 * sin(pi / 6))) / sin(pi / 6) = (-sin(pi/3)/(2*sin(pi/6)) + 1)/sin(pi/6),
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
have : tan(pi/12) = ( 1 - cos(pi/6) ) / sin(pi/6),
{
have : tan(pi/12) = tan((pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_891 (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : sin(pi/2)=sin(-pi/6)/2 + sin(pi/2)/2 - sin(-pi/3)*sin(pi/3)/(2*sin(pi/6)):=
begin
have : sin(pi / 2) / 2 + sin(-pi / 6) / 2 - sin(-pi / 3) * sin(pi / 3) / (2 * sin(pi / 6)) = sin(-pi/6)/2 + sin(pi/2)/2 - sin(-pi/3)*sin(pi/3)/(2*sin(pi/6)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : (sin(pi/6) * cos(-pi/3)) = sin(pi/6)*cos(-pi/3),
{
ring,
},
have : sin(pi / 6) * cos(-pi / 3) - sin(-pi / 3) * (sin(pi / 3) / (2 * sin(pi / 6))) = sin(pi/6)*cos(-pi/3) - sin(-pi/3)*sin(pi/3)/(2*sin(pi/6)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step2_892 : sin(-pi/9)*sin(13115*pi/36) + cos(-pi/9)*cos(13115*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(13115 * pi / 36) * sin(-pi / 9) + cos(13115 * pi / 36) * cos(-pi / 9) = sin(-pi/9)*sin(13115*pi/36) + cos(-pi/9)*cos(13115*pi/36),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4373*pi/12) = sin(13115*pi/36) * sin(-pi/9) + cos(13115*pi/36) * cos(-pi/9),
{
have : cos(4373*pi/12) = cos((13115*pi/36) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(4373*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (182),
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


lemma Trigo_number_generalization_step2_893 : -sin(-pi/3)*cos(2*pi/3) + (-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(2*pi/3)=- 4 * sin(pi/3) ** 3 + 3 * sin(pi/3):=
begin
have : -sin(-pi / 3) * cos(2 * pi / 3) + sin(2 * pi / 3) * (-sin(-pi / 6) ** 2 + cos(-pi / 6) ** 2) = -sin(-pi/3)*cos(2*pi/3) + (-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(2*pi/3),
{
field_simp at *,
ring,
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
have : sin(pi) = - 4 * sin(pi/3) ** 3 + 3 * sin(pi/3),
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
rw this,
end


lemma Trigo_number_generalization_step2_894 (h0 : cos(pi)≠ 0) : cos(2141*pi/2)/cos(pi)=0:=
begin
have : sin(pi) = cos(2141*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (534),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_895 (h0 : sin(9151*pi/14)≠ 0) (h1 : (2*sin(9151*pi/14))≠ 0) : -cos(7453*pi/14)=-sin(9151*pi/7)/(2*sin(9151*pi/14)):=
begin
have : sin(-pi/7) = -cos(7453*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/7) (266),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(9151 * pi / 7) / (2 * sin(9151 * pi / 14))) = -sin(9151*pi/7)/(2*sin(9151*pi/14)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(9151*pi/14) = sin(9151*pi/7) / ( 2 * sin(9151*pi/14) ),
{
have : sin(9151*pi/7) = sin(2*(9151*pi/14)),
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
have : sin(-pi/7) = - cos(9151*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (326),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_896 : -2*(-sin(-pi/2)*cos(-9*pi/16) + sin(-9*pi/16)*cos(-pi/2))**2 + cos(pi/4) + 1=2 * cos(-3*pi/16) * cos(pi/16):=
begin
have : (-2) * (sin((-9) * pi / 16) * cos(-pi / 2) - sin(-pi / 2) * cos((-9) * pi / 16)) ** 2 + cos(pi / 4) + 1 = -2*(-sin(-pi/2)*cos(-9*pi/16) + sin(-9*pi/16)*cos(-pi/2))**2 + cos(pi/4) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/16) = sin(-9*pi/16) * cos(-pi/2) - sin(-pi/2) * cos(-9*pi/16),
{
have : sin(-pi/16) = sin((-9*pi/16) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * sin(-pi / 16) ** 2 + cos(pi / 4) = -2*sin(-pi/16)**2 + cos(pi/4) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = 1 - 2 * sin(-pi/16) ** 2,
{
have : cos(-pi/8) = cos(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) + cos(pi/4) = 2 * cos(-3*pi/16) * cos(pi/16),
{
rw cos_add_cos,
have : cos(((-pi/8) + (pi/4))/2) = cos(pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/8) - (pi/4))/2) = cos(-3*pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_897 : 3*sin(215*pi) - 4*sin(215*pi)**3=sin(398*pi):=
begin
have : (-4) * sin(215 * pi) ** 3 + 3 * sin(215 * pi) = 3*sin(215*pi) - 4*sin(215*pi)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(645*pi) = -4 * sin(215*pi) ** 3 + 3 * sin(215*pi),
{
have : sin(645*pi) = sin(3*(215*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(645*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (321),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(398*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (200),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_898 : -1 + 2*cos(-pi/7)**2=-sin(2288*pi/7)**2 + cos(-pi/7)**2:=
begin
have : -(-sin(2288 * pi / 7)) ** 2 + cos(-pi / 7) ** 2 = -sin(2288*pi/7)**2 + cos(-pi/7)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) = -sin(2288*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/7) (163),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * cos(-pi / 7) ** 2 - 1 = -1 + 2*cos(-pi/7)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/7) = 2 * cos(-pi/7) ** 2 - 1,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/7) = - sin(-pi/7) ** 2 + cos(-pi/7) ** 2,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
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


lemma Trigo_number_generalization_step2_899 (h0 : sin(pi/4)≠ 0) (h1 : (2*sin(pi/4))≠ 0) (h2 : (2*-sin(3223*pi/4))≠ 0) (h3 : (2*sin(3223*pi/4))≠ 0) : -sin(pi/2)/(2*sin(3223*pi/4))=sqrt( 2 ) / 2:=
begin
have : sin(pi / 2) / (2 * -sin(3223 * pi / 4)) = -sin(pi/2)/(2*sin(3223*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -sin(3223*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/4) (403),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(pi/2) / ( 2 * sin(pi/4) ),
{
have : sin(pi/2) = sin(2*(pi/4)),
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_900 : -sin(-3*pi)*sin(pi) + cos(-3*pi)*cos(pi)=sin(6025*pi/2):=
begin
have : -sin((-3) * pi) * sin(pi) + cos((-3) * pi) * cos(pi) = -sin(-3*pi)*sin(pi) + cos(-3*pi)*cos(pi),
{
field_simp at *,
},
have : cos(-2*pi) = -sin(-3*pi) * sin(pi) + cos(-3*pi) * cos(pi),
{
have : cos(-2*pi) = cos((-3*pi) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2829*pi/2) = sin(6025*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (2829*pi/2) (799),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(2829*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (706),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_901 : -cos(-6227*pi/9)=- sin(-pi) * sin(pi/9) + cos(-pi) * cos(pi/9):=
begin
have : -cos((-6227) * pi / 9) = -cos(-6227*pi/9),
{
field_simp at *,
},
have : sin(33379*pi/18) = cos(-6227*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (33379*pi/18) (581),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-8*pi/9) = -sin(33379*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-8*pi/9) (926),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-8*pi/9) = - sin(-pi) * sin(pi/9) + cos(-pi) * cos(pi/9),
{
have : cos(-8*pi/9) = cos((-pi) + (pi/9)),
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


lemma Trigo_number_generalization_step2_902 : -2*sin(298*pi/3)*cos(298*pi/3)=- sqrt( 3 ) / 2:=
begin
have : -(2 * sin(298 * pi / 3) * cos(298 * pi / 3)) = -2*sin(298*pi/3)*cos(298*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(596*pi/3) = 2 * sin(298*pi/3) * cos(298*pi/3),
{
have : sin(596*pi/3) = sin(2*(298*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(596*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (99),
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


lemma Trigo_number_generalization_step2_903 : sin(-pi/9) * sin(-pi/8)=-cos(-17*pi/144)**2 - sin(pi/144)**2/2 + cos(pi/144)**2/2 + 1/2:=
begin
have : -cos((-17) * pi / 144) ** 2 + (-sin(pi / 144) ** 2 + cos(pi / 144) ** 2) / 2 + 1 / 2 = -cos(-17*pi/144)**2 - sin(pi/144)**2/2 + cos(pi/144)**2/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/72) = -sin(pi/144) ** 2 + cos(pi/144) ** 2,
{
have : cos(pi/72) = cos(2*(pi/144)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi / 72) / 2 - (2 * cos((-17) * pi / 144) ** 2 - 1) / 2 = -cos(-17*pi/144)**2 + cos(pi/72)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-17*pi/72) = 2 * cos(-17*pi/144) ** 2 - 1,
{
have : cos(-17*pi/72) = cos(2*(-17*pi/144)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) * sin(-pi/8) = cos(pi/72) / 2 - cos(-17*pi/72) / 2,
{
rw sin_mul_sin,
have : cos((-pi/9) + (-pi/8)) = cos(-17*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/9) - (-pi/8)) = cos(pi/72),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_904 : cos(895*pi/2)=-cos(4003*pi/2):=
begin
have : sin(1420*pi) = cos(4003*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1420*pi) (290),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(895*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (223),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(1420*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (710),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_905 (h0 : tan(4699*pi/14)≠ 0) (h1 : ((-1)/tan(3655*pi/7))≠ 0) (h2 : tan(3655*pi/7)≠ 0) : -tan(3655*pi/7)=- 1 / tan(8279*pi/14):=
begin
have : 1 / ((-1) / tan(3655 * pi / 7)) = -tan(3655*pi/7),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(4699*pi/14) = -1 / tan(3655*pi/7),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (4699*pi/14) (186),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/7) = 1 / tan(4699*pi/14),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/7) (335),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/7) = - 1 / tan(8279*pi/14),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/7) (591),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_906 : sin(-2*pi)*cos(6021*pi/4) + sin(11*pi/4)*cos(-2*pi)=sqrt( 2 ) / 2:=
begin
have : sin((-2) * pi) * cos(6021 * pi / 4) + sin(11 * pi / 4) * cos((-2) * pi) = sin(-2*pi)*cos(6021*pi/4) + sin(11*pi/4)*cos(-2*pi),
{
field_simp at *,
},
have : cos(11*pi/4) = cos(6021*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (11*pi/4) (754),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11 * pi / 4) * cos((-2) * pi) + sin((-2) * pi) * cos(11 * pi / 4) = sin(-2*pi)*cos(11*pi/4) + sin(11*pi/4)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(11*pi/4) * cos(-2*pi) + sin(-2*pi) * cos(11*pi/4),
{
have : sin(3*pi/4) = sin((11*pi/4) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_907 : sin(9554*pi/5) - cos(9943*pi/6)=2 * sin(4*pi/15) * cos(-pi/15):=
begin
have : sin(pi/5) = sin(9554*pi/5),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/5) (955),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(9943*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (828),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) - sin(-pi/3) = 2 * sin(4*pi/15) * cos(-pi/15),
{
rw sin_sub_sin,
have : cos(((pi/5) + (-pi/3))/2) = cos(-pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/5) - (-pi/3))/2) = sin(4*pi/15),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_908 : 1 - 2*sin(30077*pi/36)**2=sin(-pi/9) * cos(pi/3) - sin(pi/3) * cos(-pi/9):=
begin
have : cos(30077*pi/18) = 1 - 2 * sin(30077*pi/36) ** 2,
{
have : cos(30077*pi/18) = cos(2*(30077*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-4*pi/9) = cos(30077*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-4*pi/9) (835),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-4*pi/9) = sin(-pi/9) * cos(pi/3) - sin(pi/3) * cos(-pi/9),
{
have : sin(-4*pi/9) = sin((-pi/9) - (pi/3)),
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


lemma Trigo_number_generalization_step2_909 : -cos(6878*pi/3)=1 / 2:=
begin
have : sin(8353*pi/6) = -cos(6878*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (8353*pi/6) (450),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(8353*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (696),
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


lemma Trigo_number_generalization_step2_910 : 4*sin(2109*pi/4)**3 - 3*sin(2109*pi/4)=sqrt( 2 ) / 2:=
begin
have : (-4) * (-sin(2109 * pi / 4)) ** 3 + 3 * -sin(2109 * pi / 4) = 4*sin(2109*pi/4)**3 - 3*sin(2109*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -sin(2109*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi / 4) ** 3 + 3 * sin(pi / 4) = -4*sin(pi/4)**3 + 3*sin(pi/4),
{
field_simp at *,
},
have : sin(3*pi/4) = -4 * sin(pi/4) ** 3 + 3 * sin(pi/4),
{
have : sin(3*pi/4) = sin(3*(pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_911 : cos(6281*pi/14)=cos(21383*pi/14):=
begin
have : cos(5189*pi/14) = cos(6281*pi/14),
{
rw cos_eq_cos_add_int_mul_two_pi (5189*pi/14) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = cos(5189*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (185),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = cos(21383*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (763),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_912 : sin(2*pi/3)*cos(pi/2) - (cos(-pi/8)*cos(19*pi/24) - sin(-pi/8)*sin(19*pi/24))*sin(pi/2)=sin(3193*pi/6):=
begin
have : sin(2 * pi / 3) * cos(pi / 2) - sin(pi / 2) * (-sin(19 * pi / 24) * sin(-pi / 8) + cos(19 * pi / 24) * cos(-pi / 8)) = sin(2*pi/3)*cos(pi/2) - (cos(-pi/8)*cos(19*pi/24) - sin(-pi/8)*sin(19*pi/24))*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(19*pi/24) * sin(-pi/8) + cos(19*pi/24) * cos(-pi/8),
{
have : cos(2*pi/3) = cos((19*pi/24) + (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(2*pi/3) * cos(pi/2) - sin(pi/2) * cos(2*pi/3),
{
have : sin(pi/6) = sin((2*pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(3193*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (266),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_913 : (-4*sin(pi/6)**3 + 3*sin(pi/6))*sin(-pi/5)=cos(-7*pi/10)/2 + sin(5259*pi/5)/2:=
begin
have : cos((-7) * pi / 10) / 2 - -sin(5259 * pi / 5) / 2 = cos(-7*pi/10)/2 + sin(5259*pi/5)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/10) = -sin(5259*pi/5),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/10) (525),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 5) * ((-4) * sin(pi / 6) ** 3 + 3 * sin(pi / 6)) = (-4*sin(pi/6)**3 + 3*sin(pi/6))*sin(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(-pi/5) * sin(pi/2) = cos(-7*pi/10) / 2 - cos(3*pi/10) / 2,
{
rw sin_mul_sin,
have : cos((-pi/5) + (pi/2)) = cos(3*pi/10),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (pi/2)) = cos(-7*pi/10),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_914 (h0 : tan(9773*pi/12)≠ 0) (h1 : ((-1)/tan(17555*pi/12))≠ 0) (h2 : tan(17555*pi/12)≠ 0) : -tan(17555*pi/12)=2 - sqrt( 3 ):=
begin
have : 1 / ((-1) / tan(17555 * pi / 12)) = -tan(17555*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(9773*pi/12) = -1 / tan(17555*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (9773*pi/12) (648),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 1 / tan(9773*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (814),
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


lemma Trigo_number_generalization_step2_915 (h0 : tan(1423*pi/2)≠ 0) (h1 : cos(1423*pi/4)≠ 0) (h2 : (1-tan(1423*pi/4)**2)≠ 0) (h3 : (2*tan(1423*pi/4))≠ 0) (h4 : (2*tan(1423*pi/4)/(1-tan(1423*pi/4)**2))≠ 0) : (1 - tan(1423*pi/4)**2)/(2*tan(1423*pi/4))=1 / tan(51*pi/2):=
begin
have : 1 / (2 * tan(1423 * pi / 4) / (1 - tan(1423 * pi / 4) ** 2)) = (1 - tan(1423*pi/4)**2)/(2*tan(1423*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1423*pi/2) = 2 * tan(1423*pi/4) / ( 1 - tan(1423*pi/4) ** 2 ),
{
have : tan(1423*pi/2) = tan(2*(1423*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(1423*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (712),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(51*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_916 : cos(19301*pi/10)=sin(0) + sin(2*pi/5):=
begin
have : sin(2*pi/5) = cos(19301*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/5) (965),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sin(0) / 2 + sin(2 * pi / 5) / 2) = sin(0) + sin(2*pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/5) * cos(pi/5) = sin(0) / 2 + sin(2*pi/5) / 2,
{
rw sin_mul_cos,
have : sin((pi/5) + (pi/5)) = sin(2*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (pi/5)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(pi/5) * cos(pi/5)) = 2*sin(pi/5)*cos(pi/5),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(2*pi/5) = 2 * sin(pi/5) * cos(pi/5),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_917 (h0 : cos((2563*pi/3)/2)≠ 0) (h1 : sin(2563*pi/3)≠ 0) : (1 - cos(2563*pi/3))/sin(2563*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(2563*pi/6) = ( 1 - cos(2563*pi/3) ) / sin(2563*pi/3),
{
have : tan(2563*pi/6) = tan((2563*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(2563*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (427),
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


lemma Trigo_number_generalization_step2_918 (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) (h2 : (2*sin(2763*pi/2))≠ 0) : sin(2*pi)/(2*sin(2763*pi/2))=0:=
begin
have : cos(pi) = sin(2763*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (690),
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
conv {to_lhs, rw ← this,},
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_919 (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : sin(-pi/2)*sin(2*pi)/(2*cos(pi))=-sin(pi/2)*sin(pi):=
begin
have : sin(2 * pi) / (2 * cos(pi)) * sin(-pi / 2) = sin(-pi/2)*sin(2*pi)/(2*cos(pi)),
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
have : 1 / 2 * ((-2) * sin(pi / 2) * sin(pi)) = -sin(pi/2)*sin(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/2) - cos(pi/2) = -2 * sin(pi/2) * sin(pi),
{
rw cos_sub_cos,
have : sin(((3*pi/2) + (pi/2))/2) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((3*pi/2) - (pi/2))/2) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(3*pi/2) - cos(pi/2)) = cos(3*pi/2)/2-cos(pi/2)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi) * sin(-pi/2) = cos(3*pi/2) / 2 - cos(pi/2) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_number_generalization_step2_920 : cos(pi/3) - cos(pi/4)=2*sin(37439*pi/24)*cos(26645*pi/24):=
begin
have : (-2) * -sin(37439 * pi / 24) * cos(26645 * pi / 24) = 2*sin(37439*pi/24)*cos(26645*pi/24),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/24) = -sin(37439*pi/24),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/24) (780),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-2) * sin(pi / 24) * cos(26645 * pi / 24) = -2*sin(pi/24)*cos(26645*pi/24),
{
field_simp at *,
},
have : sin(7*pi/24) = cos(26645*pi/24),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/24) (555),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) - cos(pi/4) = - 2 * sin(pi/24) * sin(7*pi/24),
{
rw cos_sub_cos,
have : sin(((pi/3) + (pi/4))/2) = sin(7*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (pi/4))/2) = sin(pi/24),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_921 : -sin(pi)*cos(3631*pi/3) + sin(-2*pi/3)*cos(pi)=sin(5060*pi/3):=
begin
have : sin(pi) * -cos(3631 * pi / 3) + sin((-2) * pi / 3) * cos(pi) = -sin(pi)*cos(3631*pi/3) + sin(-2*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = -cos(3631*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/3) (605),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/3) = sin(5060*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (843),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_922 : -sin(8639*pi/6) + sin(pi/2)=-sin(-pi/6) + sin(pi/2):=
begin
have : sin(pi / 2) + -sin(8639 * pi / 6) = -sin(8639*pi/6) + sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(8639*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (720),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (-sin(-pi / 6) / 2 + sin(pi / 2) / 2) = -sin(-pi/6) + sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) * cos(pi/6) = -sin(-pi/6) / 2 + sin(pi/2) / 2,
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
conv {to_rhs, rw ← this,},
have : 2*(sin(pi/3) * cos(pi/6)) = 2*sin(pi/3)*cos(pi/6),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/2) + sin(pi/6) = 2 * sin(pi/3) * cos(pi/6),
{
rw sin_add_sin,
have : sin(((pi/2) + (pi/6))/2) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/2) - (pi/6))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_923 : tan(3958*pi/3)=sqrt( 3 ):=
begin
have : tan(1729*pi/3) = tan(3958*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (1729*pi/3) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(1729*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (576),
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


lemma Trigo_number_generalization_step2_924 : -sin(3717*pi/5)=sin(0) + sin(2*pi/5):=
begin
have : 2 * (sin(0) / 2 + sin(2 * pi / 5) / 2) = sin(0) + sin(2*pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/5) * cos(pi/5) = sin(0) / 2 + sin(2*pi/5) / 2,
{
rw sin_mul_cos,
have : sin((pi/5) + (pi/5)) = sin(2*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (pi/5)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(pi/5) * cos(pi/5)) = 2*sin(pi/5)*cos(pi/5),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(2*pi/5) = -sin(3717*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/5) (371),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/5) = 2 * sin(pi/5) * cos(pi/5),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_925 : sin(3523*pi/4)=-sin(pi/8)**2 + (-sin(pi/16)**2 + cos(pi/16)**2)**2:=
begin
have : cos(pi/8) = -sin(pi/16) ** 2 + cos(pi/16) ** 2,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = sin(3523*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/4) (440),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = - sin(pi/8) ** 2 + cos(pi/8) ** 2,
{
have : cos(pi/4) = cos(2*(pi/8)),
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


lemma Trigo_number_generalization_step2_926 (h0 : cos(9*pi/20)≠ 0) (h1 : cos(pi/5)≠ 0) (h2 : (1+tan(pi/5)*tan(9*pi/20))≠ 0) (h3 : (1+tan(9*pi/20)*tan(pi/5))≠ 0) (h4 : cos((9*pi/10)/2)≠ 0) (h5 : (1+tan(pi/5)*((1-cos(9*pi/10))/sin(9*pi/10)))≠ 0) (h6 : sin(9*pi/10)≠ 0) (h7 : (1+(1-cos(9*pi/10))*tan(pi/5)/sin(9*pi/10))≠ 0) : (-tan(pi/5) + (1 - cos(9*pi/10))/sin(9*pi/10))/(1 + (1 - cos(9*pi/10))*tan(pi/5)/sin(9*pi/10))=1 / tan(2537*pi/4):=
begin
have : (-tan(pi / 5) + (1 - cos(9 * pi / 10)) / sin(9 * pi / 10)) / (1 + tan(pi / 5) * ((1 - cos(9 * pi / 10)) / sin(9 * pi / 10))) = (-tan(pi/5) + (1 - cos(9*pi/10))/sin(9*pi/10))/(1 + (1 - cos(9*pi/10))*tan(pi/5)/sin(9*pi/10)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(9*pi/20) = ( 1 - cos(9*pi/10) ) / sin(9*pi/10),
{
have : tan(9*pi/20) = tan((9*pi/10)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(9 * pi / 20) - tan(pi / 5)) / (1 + tan(9 * pi / 20) * tan(pi / 5)) = (-tan(pi/5) + tan(9*pi/20))/(1 + tan(pi/5)*tan(9*pi/20)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = ( tan(9*pi/20) - tan(pi/5) ) / ( 1 + tan(9*pi/20) * tan(pi/5) ),
{
have : tan(pi/4) = tan((9*pi/20) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1 / tan(2537*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (634),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_927 : cos(317*pi/2)=0:=
begin
have : sin(494*pi) = cos(317*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (494*pi) (326),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(494*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (247),
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


lemma Trigo_number_generalization_step2_928 : -sin(-pi/6)**2 + cos(-pi/6)**2 + sin(3869*pi/14)=2 * cos(-5*pi/21) * cos(-2*pi/21):=
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
have : cos(pi/7) = sin(3869*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/7) (138),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(pi/7) = 2 * cos(-5*pi/21) * cos(-2*pi/21),
{
rw cos_add_cos,
have : cos(((-pi/3) + (pi/7))/2) = cos(-2*pi/21),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (pi/7))/2) = cos(-5*pi/21),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_929 : (1 - 2*sin(-pi/10)**2)*(-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))=sin(11*pi/5) / 2 + sin(9*pi/5) / 2:=
begin
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) * (1 - 2 * sin(-pi / 10) ** 2) = (1 - 2*sin(-pi/10)**2)*(-4*sin(2*pi/3)**3 + 3*sin(2*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = 1 - 2 * sin(-pi/10) ** 2,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) * cos(-pi / 5) = (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))*cos(-pi/5),
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
have : sin(2*pi) * cos(-pi/5) = sin(11*pi/5) / 2 + sin(9*pi/5) / 2,
{
rw sin_mul_cos,
have : sin((2*pi) + (-pi/5)) = sin(9*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (-pi/5)) = sin(11*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_930 (h0 : cos((pi/2)/2)≠ 0) (h1 : (cos(pi/2)+1)≠ 0) (h2 : (1+cos(pi/2))≠ 0) (h3 : (4*cos(pi/6)**3-3*cos(pi/6)+1)≠ 0) (h4 : (-3*cos(pi/6)+1+4*cos(pi/6)**3)≠ 0) : sin(pi/2)/(-3*cos(pi/6) + 1 + 4*cos(pi/6)**3)=1:=
begin
have : sin(pi / 2) / (4 * cos(pi / 6) ** 3 - 3 * cos(pi / 6) + 1) = sin(pi/2)/(-3*cos(pi/6) + 1 + 4*cos(pi/6)**3),
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
have : sin(pi / 2) / (1 + cos(pi / 2)) = sin(pi/2)/(cos(pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = sin(pi/2) / ( 1 + cos(pi/2) ),
{
have : tan(pi/4) = tan((pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_931 : -sin(-pi/4)**2 + cos(-pi/4)**2=2*sin(657*pi/2)*cos(657*pi/2):=
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
have : sin(657*pi) = 2 * sin(657*pi/2) * cos(657*pi/2),
{
have : sin(657*pi) = sin(2*(657*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(657*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (328),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_932 : sin(-pi/8)=cos(7515*pi/8):=
begin
have : cos(6347*pi/8) = cos(7515*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (6347*pi/8) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(6139*pi/8) = cos(6347*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (6139*pi/8) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) = cos(6139*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (383),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_933 : -3*sin(pi/6)*cos(pi/18) - 4*(-sin(pi/6)*cos(pi/18) + sin(pi/18)*cos(pi/6))**3 + 3*sin(pi/18)*cos(pi/6)=cos(1877*pi/6):=
begin
have : 3 * (sin(pi / 18) * cos(pi / 6) - sin(pi / 6) * cos(pi / 18)) - 4 * (sin(pi / 18) * cos(pi / 6) - sin(pi / 6) * cos(pi / 18)) ** 3 = -3*sin(pi/6)*cos(pi/18) - 4*(-sin(pi/6)*cos(pi/18) + sin(pi/18)*cos(pi/6))**3 + 3*sin(pi/18)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(pi/18) * cos(pi/6) - sin(pi/6) * cos(pi/18),
{
have : sin(-pi/9) = sin((pi/18) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(-pi/3) = cos(1877*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (156),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_934 : sin(-14*pi/45)*cos(-pi/5) - sin(-pi/5)*cos(-14*pi/45) - sin(2295*pi/7)=2 * sin(pi/63) * cos(8*pi/63):=
begin
have : sin((-14) * pi / 45) * cos(-pi / 5) - sin(-pi / 5) * cos((-14) * pi / 45) - sin(2295 * pi / 7) = sin(-14*pi/45)*cos(-pi/5) - sin(-pi/5)*cos(-14*pi/45) - sin(2295*pi/7),
{
field_simp at *,
},
have : sin(-pi/9) = sin(-14*pi/45) * cos(-pi/5) - sin(-pi/5) * cos(-14*pi/45),
{
have : sin(-pi/9) = sin((-14*pi/45) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(2295 * pi / 7) + sin(-pi / 9) = sin(-pi/9) - sin(2295*pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = -sin(2295*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/7) (164),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) + sin(-pi/9) = 2 * sin(pi/63) * cos(8*pi/63),
{
rw sin_add_sin,
have : sin(((pi/7) + (-pi/9))/2) = sin(pi/63),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/7) - (-pi/9))/2) = cos(8*pi/63),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_935 (h0 : cos((pi/3)/2)≠ 0) (h1 : (cos(pi/3)+1)≠ 0) (h2 : (1+cos(pi/3))≠ 0) (h3 : (cos(5707*pi/3)+1)≠ 0) : sin(pi/3)/(cos(5707*pi/3) + 1)=sqrt( 3 ) / 3:=
begin
have : cos(pi/3) = cos(5707*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (951),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_936 : cos(-2*pi/9)=-(3*sin(26*pi/27)*cos(pi) - 3*sin(pi)*cos(26*pi/27) - 4*(sin(26*pi/27)*cos(pi) - sin(pi)*cos(26*pi/27))**3)**2 + cos(-pi/9)**2:=
begin
have : -(3 * (sin(26 * pi / 27) * cos(pi) - sin(pi) * cos(26 * pi / 27)) - 4 * (sin(26 * pi / 27) * cos(pi) - sin(pi) * cos(26 * pi / 27)) ** 3) ** 2 + cos(-pi / 9) ** 2 = -(3*sin(26*pi/27)*cos(pi) - 3*sin(pi)*cos(26*pi/27) - 4*(sin(26*pi/27)*cos(pi) - sin(pi)*cos(26*pi/27))**3)**2 + cos(-pi/9)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/27) = sin(26*pi/27) * cos(pi) - sin(pi) * cos(26*pi/27),
{
have : sin(-pi/27) = sin((26*pi/27) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : -((-4) * sin(-pi / 27) ** 3 + 3 * sin(-pi / 27)) ** 2 + cos(-pi / 9) ** 2 = -(3*sin(-pi/27) - 4*sin(-pi/27)**3)**2 + cos(-pi/9)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = -4 * sin(-pi/27) ** 3 + 3 * sin(-pi/27),
{
have : sin(-pi/9) = sin(3*(-pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/9) = - sin(-pi/9) ** 2 + cos(-pi/9) ** 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
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


lemma Trigo_number_generalization_step2_937 (h0 : (-sin(2*pi/9)*sin(pi/9)+cos(2*pi/9)*cos(pi/9))≠ 0) (h1 : (-sin(pi/9)*sin(2*pi/9)+cos(pi/9)*cos(2*pi/9))≠ 0) (h2 : (-sin(pi/9)*sin(2*pi/9)+sin(9835*pi/18)*cos(2*pi/9))≠ 0) : sin(pi/3)/(-sin(pi/9)*sin(2*pi/9) + sin(9835*pi/18)*cos(2*pi/9))=tan(pi/3):=
begin
have : cos(pi/9) = sin(9835*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (273),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) / (-sin(2 * pi / 9) * sin(pi / 9) + cos(2 * pi / 9) * cos(pi / 9)) = sin(pi/3)/(-sin(pi/9)*sin(2*pi/9) + cos(pi/9)*cos(2*pi/9)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(2*pi/9) * sin(pi/9) + cos(2*pi/9) * cos(pi/9),
{
have : cos(pi/3) = cos((2*pi/9) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_938 : -cos(-5003*pi/4)=sqrt( 2 ) / 2:=
begin
have : -cos((-5003) * pi / 4) = -cos(-5003*pi/4),
{
field_simp at *,
},
have : sin(6973*pi/4) = cos(-5003*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (6973*pi/4) (246),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -sin(6973*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (871),
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


lemma Trigo_number_generalization_step2_939 : -3*cos(-pi/12) - sin(15837*pi/10) + 4*cos(-pi/12)**3=2 * cos(pi/40) * cos(-9*pi/40):=
begin
have : 4 * cos(-pi / 12) ** 3 - 3 * cos(-pi / 12) - sin(15837 * pi / 10) = -3*cos(-pi/12) - sin(15837*pi/10) + 4*cos(-pi/12)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = 4 * cos(-pi/12) ** 3 - 3 * cos(-pi/12),
{
have : cos(-pi/4) = cos(3*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : -sin(15837 * pi / 10) + cos(-pi / 4) = cos(-pi/4) - sin(15837*pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = -sin(15837*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (791),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) + cos(-pi/4) = 2 * cos(pi/40) * cos(-9*pi/40),
{
rw cos_add_cos,
have : cos(((-pi/5) + (-pi/4))/2) = cos(-9*pi/40),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/5) - (-pi/4))/2) = cos(pi/40),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_940 (h0 : tan(1730*pi/3)≠ 0) (h1 : tan(2696*pi/3)≠ 0) : -1/tan(2696*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(2696 * pi / 3) = -1/tan(2696*pi/3),
{
field_simp at *,
},
have : tan(1730*pi/3) = tan(2696*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (1730*pi/3) (322),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(1730 * pi / 3) = -1/tan(1730*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1730*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (576),
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


lemma Trigo_number_generalization_step2_941 : cos(-pi/6)*cos(5*pi/12) - (-4*sin(5*pi/36)**3 + 3*sin(5*pi/36))*sin(-pi/6)=sqrt( 2 ) / 2:=
begin
have : cos(-pi / 6) * cos(5 * pi / 12) - sin(-pi / 6) * ((-4) * sin(5 * pi / 36) ** 3 + 3 * sin(5 * pi / 36)) = cos(-pi/6)*cos(5*pi/12) - (-4*sin(5*pi/36)**3 + 3*sin(5*pi/36))*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = -4 * sin(5*pi/36) ** 3 + 3 * sin(5*pi/36),
{
have : sin(5*pi/12) = sin(3*(5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 12) * sin(-pi / 6) + cos(5 * pi / 12) * cos(-pi / 6) = cos(-pi/6)*cos(5*pi/12) - sin(-pi/6)*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(5*pi/12) * sin(-pi/6) + cos(5*pi/12) * cos(-pi/6),
{
have : cos(pi/4) = cos((5*pi/12) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step2_942 : -cos(1231*pi/4)**2 + sin(1231*pi/4)**2=0:=
begin
have : -(-sin(1231 * pi / 4) ** 2 + cos(1231 * pi / 4) ** 2) = -cos(1231*pi/4)**2 + sin(1231*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1231*pi/2) = -sin(1231*pi/4) ** 2 + cos(1231*pi/4) ** 2,
{
have : cos(1231*pi/2) = cos(2*(1231*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(1231*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (307),
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


lemma Trigo_number_generalization_step2_943 : -sin(pi/5)*cos(-9*pi/5) + sin(-9*pi/5)*cos(pi/5)=cos(3297*pi/2):=
begin
have : sin((-9) * pi / 5) * cos(pi / 5) - sin(pi / 5) * cos((-9) * pi / 5) = -sin(pi/5)*cos(-9*pi/5) + sin(-9*pi/5)*cos(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-9*pi/5) * cos(pi/5) - sin(pi/5) * cos(-9*pi/5),
{
have : sin(-2*pi) = sin((-9*pi/5) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(793*pi/2) = cos(3297*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (793*pi/2) (626),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = cos(793*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (197),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_944 (h0 : sin(-pi/2)≠ 0) (h1 : (2*sin(-pi/2))≠ 0) : sin(-pi)/(2*sin(-pi/2))=3*sin(1222*pi/3) - 4*sin(1222*pi/3)**3:=
begin
have : 4 * (-sin(1222 * pi / 3)) ** 3 - 3 * -sin(1222 * pi / 3) = 3*sin(1222*pi/3) - 4*sin(1222*pi/3)**3,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(1222*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (203),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_number_generalization_step2_945 (h0 : cos(pi/6)≠ 0) (h1 : (-3*cos(pi/18)+4*cos(pi/18)**3)≠ 0) (h2 : (4*cos(pi/18)**3-3*cos(pi/18))≠ 0) : sin(pi/6)/(-3*cos(pi/18) + 4*cos(pi/18)**3)=sqrt( 3 ) / 3:=
begin
have : sin(pi / 6) / (4 * cos(pi / 18) ** 3 - 3 * cos(pi / 18)) = sin(pi/6)/(-3*cos(pi/18) + 4*cos(pi/18)**3),
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
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_946 : -sin(10739*pi/6)=2 * cos(-pi/6) ** 2 - 1:=
begin
have : cos(4243*pi/3) = -sin(10739*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (4243*pi/3) (187),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(4243*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (707),
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


lemma Trigo_number_generalization_step2_947 (h0 : cos((pi/6)/2)≠ 0) (h1 : sin(pi/6)≠ 0) : (1 - cos(5605*pi/6))/sin(pi/6)=2 - sqrt( 3 ):=
begin
have : cos(pi/6) = cos(5605*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (467),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( 1 - cos(pi/6) ) / sin(pi/6),
{
have : tan(pi/12) = tan((pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step2_948 : -cos(5534*pi/3)=1 / 2:=
begin
have : sin(3799*pi/6) = cos(5534*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3799*pi/6) (605),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(3799*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (316),
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


lemma Trigo_number_generalization_step2_949 : -cos(4100*pi/7)**2 + sin(4100*pi/7)**2=4 * cos(-pi/7) ** 3 - 3 * cos(-pi/7):=
begin
have : -(-sin(4100 * pi / 7) ** 2 + cos(4100 * pi / 7) ** 2) = -cos(4100*pi/7)**2 + sin(4100*pi/7)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(8200*pi/7) = -sin(4100*pi/7) ** 2 + cos(4100*pi/7) ** 2,
{
have : cos(8200*pi/7) = cos(2*(4100*pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/7) = -cos(8200*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3*pi/7) (585),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/7) = 4 * cos(-pi/7) ** 3 - 3 * cos(-pi/7),
{
have : cos(-3*pi/7) = cos(3*(-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_950 : cos(-3535*pi/4)=cos(3135*pi/4):=
begin
have : cos((-3535) * pi / 4) = cos(-3535*pi/4),
{
field_simp at *,
},
have : sin(4105*pi/4) = cos(-3535*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4105*pi/4) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(4105*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (513),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = cos(3135*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/4) (392),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_951 : cos(pi/7)=sin(-8027*pi/14):=
begin
have : - -sin((-8027) * pi / 14) = sin(-8027*pi/14),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(28943*pi/14) = -sin(-8027*pi/14),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (28943*pi/14) (747),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5899*pi/14) = sin(28943*pi/14),
{
rw sin_eq_sin_add_int_mul_two_pi (5899*pi/14) (823),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = - sin(5899*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (210),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_952 : -sin(2111*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3297*pi/4) = -sin(2111*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (3297*pi/4) (676),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(3297*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (412),
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


lemma Trigo_number_generalization_step2_953 : -sin(pi/6)*cos(2545*pi/3) + cos(-pi/6)*cos(pi/6)=1 / 2:=
begin
have : -cos(2545 * pi / 3) * sin(pi / 6) + cos(-pi / 6) * cos(pi / 6) = -sin(pi/6)*cos(2545*pi/3) + cos(-pi/6)*cos(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(2545*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (424),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) * sin(-pi / 6) + cos(pi / 6) * cos(-pi / 6) = sin(-pi/6)*sin(pi/6) + cos(-pi/6)*cos(pi/6),
{
field_simp at *,
ring,
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
conv {to_lhs, rw ← this,},
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_954 : -sin(4593*pi/10)=cos(4429*pi/5):=
begin
have : cos(1961*pi/5) = -sin(4593*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1961*pi/5) (425),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = cos(1961*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/5) (196),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = cos(4429*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/5) (443),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_955 : 1 - 2*sin(-pi/9)**2=-cos(-4*pi/9)/2 + cos(-2*pi/9)/2 + cos(-pi/3)*cos(-pi/9):=
begin
have : cos((-2) * pi / 9) / 2 - cos((-4) * pi / 9) / 2 + cos(-pi / 3) * cos(-pi / 9) = -cos(-4*pi/9)/2 + cos(-2*pi/9)/2 + cos(-pi/3)*cos(-pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) * sin(-pi/9) = cos(-2*pi/9) / 2 - cos(-4*pi/9) / 2,
{
rw sin_mul_sin,
have : cos((-pi/3) + (-pi/9)) = cos(-4*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/3) - (-pi/9)) = cos(-2*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (sin(-pi/3) * sin(-pi/9)) = sin(-pi/3)*sin(-pi/9),
{
ring,
},
have : cos(-2*pi/9) = 1 - 2 * sin(-pi/9) ** 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/9) = sin(-pi/3) * sin(-pi/9) + cos(-pi/3) * cos(-pi/9),
{
have : cos(-2*pi/9) = cos((-pi/3) - (-pi/9)),
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


lemma Trigo_number_generalization_step2_956 : -sin(-11*pi/9)/2 + sin(-pi)/2 + sin(-10*pi/9)*cos(pi/9)=- sin(1731*pi):=
begin
have : -sin((-11) * pi / 9) / 2 + sin(-pi) / 2 + sin((-10) * pi / 9) * cos(pi / 9) = -sin(-11*pi/9)/2 + sin(-pi)/2 + sin(-10*pi/9)*cos(pi/9),
{
field_simp at *,
},
have : sin(pi/9) * cos(-10*pi/9) = -sin(-11*pi/9) / 2 + sin(-pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-10*pi/9) + (pi/9)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-10*pi/9) - (pi/9)) = sin(-11*pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/9) * cos(-10*pi/9)) = sin(pi/9)*cos(-10*pi/9),
{
ring,
},
have : sin((-10) * pi / 9) * cos(pi / 9) + sin(pi / 9) * cos((-10) * pi / 9) = sin(pi/9)*cos(-10*pi/9) + sin(-10*pi/9)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(-10*pi/9) * cos(pi/9) + sin(pi/9) * cos(-10*pi/9),
{
have : sin(-pi) = sin((-10*pi/9) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(1731*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (865),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_957 : -sin(1801*pi/3)/2 - sin(600*pi)/2=sin(-pi/3) / 2 + sin(0) / 2:=
begin
have : -(sin(600 * pi) / 2 + sin(1801 * pi / 3) / 2) = -sin(1801*pi/3)/2 - sin(600*pi)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3601*pi/6) * cos(pi/6) = sin(600*pi) / 2 + sin(1801*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((3601*pi/6) + (pi/6)) = sin(1801*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((3601*pi/6) - (pi/6)) = sin(600*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(3601*pi/6) * cos(pi/6)) = -sin(3601*pi/6)*cos(pi/6),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(-pi/6) = -sin(3601*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (300),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(pi/6) = sin(-pi/3) / 2 + sin(0) / 2,
{
rw sin_mul_cos,
have : sin((-pi/6) + (pi/6)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (pi/6)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_958 (h0 : cos(2849*pi/4)≠ 0) : -sin(2849*pi/4)/cos(2849*pi/4)=- 1:=
begin
have : -(sin(2849 * pi / 4) / cos(2849 * pi / 4)) = -sin(2849*pi/4)/cos(2849*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2849*pi/4) = sin(2849*pi/4) / cos(2849*pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = -tan(2849*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (713),
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


lemma Trigo_number_generalization_step2_959 : -sin(8896*pi/5)=- cos(2547*pi/10):=
begin
have : cos(12267*pi/10) = sin(8896*pi/5),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (12267*pi/10) (276),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = -cos(12267*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/5) (613),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = - cos(2547*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/5) (127),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_960 : cos(1839*pi/2)=- sin(969*pi):=
begin
have : - -cos(1839 * pi / 2) = cos(1839*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(16*pi) = -cos(1839*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (16*pi) (467),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(16*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(969*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (485),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_961 : (-sin(-pi/16)**2 + cos(-pi/16)**2)*sin(2299*pi/2)=cos(9*pi/8) / 2 + cos(7*pi/8) / 2:=
begin
have : sin(2299 * pi / 2) * (-sin(-pi / 16) ** 2 + cos(-pi / 16) ** 2) = (-sin(-pi/16)**2 + cos(-pi/16)**2)*sin(2299*pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = -sin(-pi/16) ** 2 + cos(-pi/16) ** 2,
{
have : cos(-pi/8) = cos(2*(-pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(2299*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (574),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * cos(-pi/8) = cos(9*pi/8) / 2 + cos(7*pi/8) / 2,
{
rw cos_mul_cos,
have : cos((pi) + (-pi/8)) = cos(7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (-pi/8)) = cos(9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_962 : sin(2517*pi/2)=1 - 2*cos(3325*pi/2)**2:=
begin
have : cos(2*pi) = sin(2517*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (628),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(3325*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (830),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = 1 - 2 * sin(pi) ** 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step2_963 : -2*sin(-pi)*cos(-pi)=- 4 * sin(-pi) ** 3 + 3 * sin(-pi):=
begin
have : -(2 * sin(-pi) * cos(-pi)) = -2*sin(-pi)*cos(-pi),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : -sin((-2) * pi) = -sin(-2*pi),
{
field_simp at *,
},
have : sin(-3*pi) = -sin(-2*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-3*pi) (0),
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


lemma Trigo_number_generalization_step2_964 : sin(-2*pi)*cos(9959*pi/5) - sin(9959*pi/5)*cos(-2*pi)=- cos(19733*pi/10):=
begin
have : -(sin(9959 * pi / 5) * cos((-2) * pi) - sin((-2) * pi) * cos(9959 * pi / 5)) = sin(-2*pi)*cos(9959*pi/5) - sin(9959*pi/5)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(9969*pi/5) = sin(9959*pi/5) * cos(-2*pi) - sin(-2*pi) * cos(9959*pi/5),
{
have : sin(9969*pi/5) = sin((9959*pi/5) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = -sin(9969*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/5) (997),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = - cos(19733*pi/10),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (986),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_965 (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : -sin(2*pi)*sin(2536*pi/3)/(2*cos(pi))=sin(5*pi/6) / 2 + sin(7*pi/6) / 2:=
begin
have : -(sin(2 * pi) / (2 * cos(pi))) * sin(2536 * pi / 3) = -sin(2*pi)*sin(2536*pi/3)/(2*cos(pi)),
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
have : sin(pi) * -sin(2536 * pi / 3) = -sin(pi)*sin(2536*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(2536*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (422),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * cos(pi/6) = sin(5*pi/6) / 2 + sin(7*pi/6) / 2,
{
rw sin_mul_cos,
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
},
rw this,
end


lemma Trigo_number_generalization_step2_966 : -cos(9898*pi/5)=4 * cos(-pi/5) ** 3 - 3 * cos(-pi/5):=
begin
have : cos(7658*pi/5) = cos(9898*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (7658*pi/5) (224),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/5) = -cos(7658*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3*pi/5) (765),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/5) = 4 * cos(-pi/5) ** 3 - 3 * cos(-pi/5),
{
have : cos(-3*pi/5) = cos(3*(-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_967 : -sin(-pi)*cos(-pi/2) - cos(-pi)*cos(1612*pi)=sin(1593*pi/2):=
begin
have : -sin(-pi) * cos(-pi / 2) + -cos(1612 * pi) * cos(-pi) = -sin(-pi)*cos(-pi/2) - cos(-pi)*cos(1612*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(1612*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (805),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) * cos(-pi) - sin(-pi) * cos(-pi / 2) = -sin(-pi)*cos(-pi/2) + sin(-pi/2)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(-pi/2) * cos(-pi) - sin(-pi) * cos(-pi/2),
{
have : sin(pi/2) = sin((-pi/2) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(1593*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_968 : -3*cos(pi/12) + cos(-pi/7) + 4*cos(pi/12)**3=cos(pi/4) + cos(pi/7):=
begin
have : 2 * (cos(pi / 7) / 2 + cos(pi / 4) / 2) = cos(pi/4) + cos(pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(11*pi/56) * cos(3*pi/56) = cos(pi/7) / 2 + cos(pi/4) / 2,
{
rw cos_mul_cos,
have : cos((11*pi/56) + (3*pi/56)) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((11*pi/56) - (3*pi/56)) = cos(pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(cos(11*pi/56) * cos(3*pi/56)) = 2*cos(11*pi/56)*cos(3*pi/56),
{
ring,
},
conv {to_rhs, rw this,},
have : 4 * cos(pi / 12) ** 3 - 3 * cos(pi / 12) + cos(-pi / 7) = -3*cos(pi/12) + cos(-pi/7) + 4*cos(pi/12)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : cos(pi/4) + cos(-pi/7) = 2 * cos(11*pi/56) * cos(3*pi/56),
{
rw cos_add_cos,
have : cos(((pi/4) + (-pi/7))/2) = cos(3*pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/4) - (-pi/7))/2) = cos(11*pi/56),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_969 : cos(12*pi/35)*cos(16953*pi/10) + sin(pi/5) + sin(12*pi/35)*cos(-pi/5)=2 * sin(6*pi/35) * cos(pi/35):=
begin
have : cos(16953 * pi / 10) * cos(12 * pi / 35) + sin(pi / 5) + sin(12 * pi / 35) * cos(-pi / 5) = cos(12*pi/35)*cos(16953*pi/10) + sin(pi/5) + sin(12*pi/35)*cos(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = cos(16953*pi/10),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (847),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 5) + (sin(12 * pi / 35) * cos(-pi / 5) + sin(-pi / 5) * cos(12 * pi / 35)) = sin(-pi/5)*cos(12*pi/35) + sin(pi/5) + sin(12*pi/35)*cos(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(12*pi/35) * cos(-pi/5) + sin(-pi/5) * cos(12*pi/35),
{
have : sin(pi/7) = sin((12*pi/35) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) + sin(pi/7) = 2 * sin(6*pi/35) * cos(pi/35),
{
rw sin_add_sin,
have : sin(((pi/5) + (pi/7))/2) = sin(6*pi/35),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/5) - (pi/7))/2) = cos(pi/35),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_970 : sin(1354*pi)=0:=
begin
have : sin(265*pi) = sin(1354*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (265*pi) (809),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(265*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (132),
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


lemma Trigo_number_generalization_step2_971 (h0 : tan(475*pi/4)≠ 0) (h1 : cos(1427*pi/12)≠ 0) (h2 : cos(pi/6)≠ 0) (h3 : (1+tan(1427*pi/12)*tan(pi/6))≠ 0) (h4 : ((tan(1427*pi/12)-tan(pi/6))/(1+tan(1427*pi/12)*tan(pi/6)))≠ 0) (h5 : (-tan(pi/6)+tan(1427*pi/12))≠ 0) : (tan(pi/6)*tan(1427*pi/12) + 1)/(-tan(pi/6) + tan(1427*pi/12))=- 1:=
begin
have : 1 / ((tan(1427 * pi / 12) - tan(pi / 6)) / (1 + tan(1427 * pi / 12) * tan(pi / 6))) = (tan(pi/6)*tan(1427*pi/12) + 1)/(-tan(pi/6) + tan(1427*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(475*pi/4) = ( tan(1427*pi/12) - tan(pi/6) ) / ( 1 + tan(1427*pi/12) * tan(pi/6) ),
{
have : tan(475*pi/4) = tan((1427*pi/12) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 1 / tan(475*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (119),
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


lemma Trigo_number_generalization_step2_972 : sin(-7*pi/18)*cos(-pi/9) + sin(-pi/9)*cos(-7*pi/18)=cos(-289*pi):=
begin
have : sin((-7) * pi / 18) * cos(-pi / 9) + sin(-pi / 9) * cos((-7) * pi / 18) = sin(-7*pi/18)*cos(-pi/9) + sin(-pi/9)*cos(-7*pi/18),
{
field_simp at *,
},
have : sin(-pi/2) = sin(-7*pi/18) * cos(-pi/9) + sin(-pi/9) * cos(-7*pi/18),
{
have : sin(-pi/2) = sin((-7*pi/18) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos((-289) * pi) = cos(-289*pi),
{
field_simp at *,
},
have : cos(897*pi) = cos(-289*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (897*pi) (304),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = cos(897*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (448),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_973 : sin(2585*pi/6)=-1 + 2*cos(1457*pi/6)**2:=
begin
have : 2 * cos(1457 * pi / 6) ** 2 - 1 = -1 + 2*cos(1457*pi/6)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(1457*pi/3) = 2 * cos(1457*pi/6) ** 2 - 1,
{
have : cos(1457*pi/3) = cos(2*(1457*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = sin(2585*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (215),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(1457*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (243),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_974 : sin(2881*pi/2)=2 * cos(-pi) ** 2 - 1:=
begin
have : - -sin(2881 * pi / 2) = sin(2881*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(875*pi) = -sin(2881*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (875*pi) (282),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(875*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (438),
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


lemma Trigo_number_generalization_step2_975 : (3*sin(-pi/9) - 4*sin(-pi/9)**3)**2=1/2 - sin(3343*pi/6)/2:=
begin
have : ((-4) * sin(-pi / 9) ** 3 + 3 * sin(-pi / 9)) ** 2 = (3*sin(-pi/9) - 4*sin(-pi/9)**3)**2,
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
have : cos(-2*pi/3) = sin(3343*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi/3) (278),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_number_generalization_step2_976 : -sin(6137*pi/6)**2 + cos(pi/6)**2=- sin(419*pi/6):=
begin
have : sin(pi/6) = sin(6137*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (511),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/3) = - sin(419*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_977 : -cos(19857*pi/10)=- sin(6064*pi/5):=
begin
have : cos(15787*pi/10) = -cos(19857*pi/10),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (15787*pi/10) (203),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = cos(15787*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/5) (789),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = - sin(6064*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/5) (606),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_978 : -1 + 2*cos(4453*pi/6)**2=1 / 2:=
begin
have : cos(pi/6) = cos(4453*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (371),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(pi / 6) ** 2 - 1 = -1 + 2*cos(pi/6)**2,
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_979 : -sin(3*pi/40)*sin(pi/8) + cos(3*pi/40)*cos(11359*pi/8)=- cos(4004*pi/5):=
begin
have : cos(pi/8) = cos(11359*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/8) (710),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = -sin(3*pi/40) * sin(pi/8) + cos(3*pi/40) * cos(pi/8),
{
have : cos(pi/5) = cos((3*pi/40) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = - cos(4004*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/5) (400),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_980 : cos(-pi/9)*cos(12874*pi/9) - sin(-pi/9)*sin(12874*pi/9)=cos(5849*pi/3):=
begin
have : -sin(12874 * pi / 9) * sin(-pi / 9) + cos(12874 * pi / 9) * cos(-pi / 9) = cos(-pi/9)*cos(12874*pi/9) - sin(-pi/9)*sin(12874*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4291*pi/3) = -sin(12874*pi/9) * sin(-pi/9) + cos(12874*pi/9) * cos(-pi/9),
{
have : cos(4291*pi/3) = cos((12874*pi/9) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(4291*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (715),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(5849*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (975),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_981 (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) (h2 : sin(pi/6)≠ 0) (h3 : (2*sin(pi/6))≠ 0) (h4 : (2*(sin(pi/3)/(2*sin(pi/6))))≠ 0) : sin(pi/6)=1 / 2:=
begin
have : sin(pi / 3) / (2 * (sin(pi / 3) / (2 * sin(pi / 6)))) = sin(pi/6),
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
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step2_982 (h0 : cos((2*pi)/2)≠ 0) (h1 : (1+cos(2*pi))≠ 0) : -cos(2427*pi/2)/(1 + cos(2*pi))=0:=
begin
have : sin(2*pi) = -cos(2427*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (607),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(2*pi) / ( 1 + cos(2*pi) ),
{
have : tan(pi) = tan((2*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step2_983 : sin(1363*pi/4) + cos(7663*pi/8)=2 * cos(-pi/16) * cos(3*pi/16):=
begin
have : cos(pi/4) = sin(1363*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/4) (170),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7663 * pi / 8) + cos(pi / 4) = cos(pi/4) + cos(7663*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = cos(7663*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/8) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) + cos(pi/4) = 2 * cos(-pi/16) * cos(3*pi/16),
{
rw cos_add_cos,
have : cos(((pi/8) + (pi/4))/2) = cos(3*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/8) - (pi/4))/2) = cos(-pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_984 : -sin(3309*pi/2)=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : sin(83*pi/2) = -sin(3309*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (83*pi/2) (848),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = sin(83*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = 4 * cos(pi) ** 3 - 3 * cos(pi),
{
have : cos(3*pi) = cos(3*(pi)),
{
apply congr_arg,
ring,
},
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step2_985 : -sin(pi/8)*sin(3*pi/8) - sin(14173*pi/8)*cos(3*pi/8)=0:=
begin
have : -sin(pi / 8) * sin(3 * pi / 8) + -sin(14173 * pi / 8) * cos(3 * pi / 8) = -sin(pi/8)*sin(3*pi/8) - sin(14173*pi/8)*cos(3*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(14173*pi/8),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (885),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(3 * pi / 8) * sin(pi / 8) + cos(3 * pi / 8) * cos(pi / 8) = -sin(pi/8)*sin(3*pi/8) + cos(pi/8)*cos(3*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(3*pi/8) * sin(pi/8) + cos(3*pi/8) * cos(pi/8),
{
have : cos(pi/2) = cos((3*pi/8) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step2_986 : 2*sin(pi/14)*cos(pi/14)=sin(18803*pi/7):=
begin
have : sin(pi/7) = 2 * sin(pi/14) * cos(pi/14),
{
have : sin(pi/7) = sin(2*(pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(17411*pi/14) = sin(18803*pi/7),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (17411*pi/14) (721),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = cos(17411*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (621),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_987 : sin(-pi/2) + sin(-pi/4)=-2*sin(-3*pi/8)*sin(11805*pi/8):=
begin
have : (-2) * sin((-3) * pi / 8) * sin(11805 * pi / 8) = -2*sin(-3*pi/8)*sin(11805*pi/8),
{
field_simp at *,
},
have : cos(1799*pi/8) = sin(11805*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (1799*pi/8) (850),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin((-3) * pi / 8) * -cos(1799 * pi / 8) = -2*sin(-3*pi/8)*cos(1799*pi/8),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = -cos(1799*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/8) (112),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) + sin(-pi/4) = 2 * sin(-3*pi/8) * cos(-pi/8),
{
rw sin_add_sin,
have : sin(((-pi/2) + (-pi/4))/2) = sin(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/2) - (-pi/4))/2) = cos(-pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step2_988 (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : sin(pi/3)=sqrt( 3 ) / 2:=
begin
have : 2 * sin(pi / 6) * (sin(pi / 3) / (2 * sin(pi / 6))) = sin(pi/3),
{
field_simp at *,
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
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step2_989 : cos(pi/3)=sin(7973*pi/6):=
begin
have : sin(1385*pi/6) = sin(7973*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (1385*pi/6) (549),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(8389*pi/6) = sin(1385*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8389*pi/6) (814),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(8389*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (699),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_990 : (cos(pi/2)*cos(11*pi/18) + sin(pi/2)*sin(11*pi/18))*sin(17*pi/9) + sin(pi/9)*cos(17*pi/9)=- cos(1221*pi/2):=
begin
have : sin(17 * pi / 9) * (sin(11 * pi / 18) * sin(pi / 2) + cos(11 * pi / 18) * cos(pi / 2)) + sin(pi / 9) * cos(17 * pi / 9) = (cos(pi/2)*cos(11*pi/18) + sin(pi/2)*sin(11*pi/18))*sin(17*pi/9) + sin(pi/9)*cos(17*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = sin(11*pi/18) * sin(pi/2) + cos(11*pi/18) * cos(pi/2),
{
have : cos(pi/9) = cos((11*pi/18) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(17*pi/9) * cos(pi/9) + sin(pi/9) * cos(17*pi/9),
{
have : sin(2*pi) = sin((17*pi/9) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(1221*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (304),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_991 : -cos(-2395*pi/2)=- sin(888*pi):=
begin
have : -cos((-2395) * pi / 2) = -cos(-2395*pi/2),
{
field_simp at *,
},
have : sin(1236*pi) = cos(-2395*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (1236*pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(1236*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (619),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(888*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (445),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step2_992 (h0 : cos((2711*pi/2)/2)≠ 0) (h1 : (cos(2711*pi/2)+1)≠ 0) (h2 : (1+cos(2711*pi/2))≠ 0) : -sin(2711*pi/2)/(cos(2711*pi/2) + 1)=1:=
begin
have : -(sin(2711 * pi / 2) / (1 + cos(2711 * pi / 2))) = -sin(2711*pi/2)/(cos(2711*pi/2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2711*pi/4) = sin(2711*pi/2) / ( 1 + cos(2711*pi/2) ),
{
have : tan(2711*pi/4) = tan((2711*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = -tan(2711*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (678),
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


lemma Trigo_number_generalization_step2_993 : sin(-403*pi/6)=1 / 2:=
begin
have : - -sin((-403) * pi / 6) = sin(-403*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(806*pi/3) = -sin(-403*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (806*pi/3) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(806*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (134),
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


lemma Trigo_number_generalization_step2_994 : cos(593*pi)=- 1:=
begin
have : - -cos(593 * pi) = cos(593*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2557*pi/2) = -cos(593*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2557*pi/2) (935),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(2557*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (638),
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


lemma Trigo_number_generalization_step2_995 : sin(1973*pi/2)=1:=
begin
have : - -sin(1973 * pi / 2) = sin(1973*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(185*pi) = -sin(1973*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (185*pi) (585),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(185*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (92),
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


lemma Trigo_number_generalization_step2_996 : sin(-pi/3) + sin(-243*pi)=2 * sin(-7*pi/6) * cos(-5*pi/6):=
begin
have : sin(-pi / 3) + sin((-243) * pi) = sin(-pi/3) + sin(-243*pi),
{
field_simp at *,
},
have : cos(3555*pi/2) = sin(-243*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3555*pi/2) (767),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3555 * pi / 2) + sin(-pi / 3) = sin(-pi/3) + cos(3555*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(3555*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (889),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) + sin(-pi/3) = 2 * sin(-7*pi/6) * cos(-5*pi/6),
{
rw sin_add_sin,
have : sin(((-2*pi) + (-pi/3))/2) = sin(-7*pi/6),
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
},
rw this,
end


lemma Trigo_number_generalization_step2_997 (h0 : tan(1121*pi/3)≠ 0) (h1 : (sin(1121*pi/3)/cos(1121*pi/3))≠ 0) (h2 : cos(1121*pi/3)≠ 0) (h3 : sin(1121*pi/3)≠ 0) : -cos(1121*pi/3)/sin(1121*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / (sin(1121 * pi / 3) / cos(1121 * pi / 3)) = -cos(1121*pi/3)/sin(1121*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1121*pi/3) = sin(1121*pi/3) / cos(1121*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(1121 * pi / 3) = -1/tan(1121*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1121*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (373),
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


lemma Trigo_number_generalization_step2_998 (h0 : cos(-pi/9)≠ 0) : tan(-pi/9)=(cos(-pi/3)*cos(30473*pi/18) - sin(-pi/3)*sin(30473*pi/18))/cos(-pi/9):=
begin
have : (-sin(30473 * pi / 18) * sin(-pi / 3) + cos(30473 * pi / 18) * cos(-pi / 3)) / cos(-pi / 9) = (cos(-pi/3)*cos(30473*pi/18) - sin(-pi/3)*sin(30473*pi/18))/cos(-pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(30467*pi/18) = -sin(30473*pi/18) * sin(-pi/3) + cos(30473*pi/18) * cos(-pi/3),
{
have : cos(30467*pi/18) = cos((30473*pi/18) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = cos(30467*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/9) (846),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/9) = sin(-pi/9) / cos(-pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step2_999 : -1 + 2*sin(10399*pi/24)**2=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(1 - 2 * sin(10399 * pi / 24) ** 2) = -1 + 2*sin(10399*pi/24)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(10399*pi/12) = 1 - 2 * sin(10399*pi/24) ** 2,
{
have : cos(10399*pi/12) = cos(2*(10399*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(10399*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/12) (433),
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
