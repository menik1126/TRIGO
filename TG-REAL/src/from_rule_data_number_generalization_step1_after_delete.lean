import trigo_import
open real
open_locale real
variables (x y : ℝ)



lemma Trigo_number_generalization_step1_0 (h0 : cos(-pi/3)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan(-pi/2)*tan(-pi/3))≠ 0) (h3 : (1+tan(-pi/3)*tan(-pi/2))≠ 0) : sin(pi/6) / cos(pi/6)=(tan(-pi/3) - tan(-pi/2))/(1 + tan(-pi/2)*tan(-pi/3)):=
begin
have : (tan(-pi / 3) - tan(-pi / 2)) / (1 + tan(-pi / 3) * tan(-pi / 2)) = (tan(-pi/3) - tan(-pi/2))/(1 + tan(-pi/2)*tan(-pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/6) = ( tan(-pi/3) - tan(-pi/2) ) / ( 1 + tan(-pi/3) * tan(-pi/2) ),
{
have : tan(pi/6) = tan((-pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) / cos(pi/6) = tan(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_1 (h0 : cos(pi/3)≠ 0) : sin(pi/3)/cos(pi/3)=sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_2 : cos(613*pi/4)=cos(2627*pi/4):=
begin
have : sin(-pi/4) = cos(613*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = cos(2627*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (328),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_3 (h0 : cos((3*pi/2)/2)≠ 0) (h1 : (1+cos(3*pi/2))≠ 0) (h2 : (cos(3*pi/2)+1)≠ 0) : sin(3*pi/2)/(cos(3*pi/2) + 1)=- 1:=
begin
have : sin(3 * pi / 2) / (1 + cos(3 * pi / 2)) = sin(3*pi/2)/(cos(3*pi/2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = sin(3*pi/2) / ( 1 + cos(3*pi/2) ),
{
have : tan(3*pi/4) = tan((3*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_4 : cos(pi/4)=-cos(8011*pi/4):=
begin
have : sin(7153*pi/4) = -cos(8011*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (7153*pi/4) (107),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = sin(7153*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (894),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_5 : -sin(3875*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -sin(3875*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (484),
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


lemma Trigo_number_generalization_step1_6 : cos(-2*pi/5)=1 - 2*cos(17763*pi/10)**2:=
begin
have : 1 - 2 * (-cos(17763 * pi / 10)) ** 2 = 1 - 2*cos(17763*pi/10)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/5) = -cos(17763*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/5) (888),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_7 (h0 : cos(5*pi/18)≠ 0) (h1 : cos(pi/9)≠ 0) (h2 : (1+tan(5*pi/18)*tan(pi/9))≠ 0) (h3 : (tan(pi/9)*tan(5*pi/18)+1)≠ 0) : (-tan(pi/9) + tan(5*pi/18))/(tan(pi/9)*tan(5*pi/18) + 1)=sqrt( 3 ) / 3:=
begin
have : (tan(5 * pi / 18) - tan(pi / 9)) / (1 + tan(5 * pi / 18) * tan(pi / 9)) = (-tan(pi/9) + tan(5*pi/18))/(tan(pi/9)*tan(5*pi/18) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(5*pi/18) - tan(pi/9) ) / ( 1 + tan(5*pi/18) * tan(pi/9) ),
{
have : tan(pi/6) = tan((5*pi/18) - (pi/9)),
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


lemma Trigo_number_generalization_step1_8 : -cos(2473*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(2473*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (206),
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


lemma Trigo_number_generalization_step1_9 : sin(-pi/8) * sin(pi)=-sin(-pi)*sin(-pi/8):=
begin
have : 1 / 2 * ((-2) * sin(-pi) * sin(-pi / 8)) = -sin(-pi)*sin(-pi/8),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-9*pi/8) - cos(7*pi/8) = -2 * sin(-pi) * sin(-pi/8),
{
rw cos_sub_cos,
have : sin(((-9*pi/8) + (7*pi/8))/2) = sin(-pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-9*pi/8) - (7*pi/8))/2) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(-9*pi/8) - cos(7*pi/8)) = cos(-9*pi/8)/2-cos(7*pi/8)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi/8) * sin(pi) = cos(-9*pi/8) / 2 - cos(7*pi/8) / 2,
{
rw sin_mul_sin,
have : cos((-pi/8) + (pi)) = cos(7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/8) - (pi)) = cos(-9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_10 : -sin(pi/9)*cos(14*pi/45) + sin(14*pi/45)*cos(pi/9)=- sin(8779*pi/5):=
begin
have : sin(14 * pi / 45) * cos(pi / 9) - sin(pi / 9) * cos(14 * pi / 45) = -sin(pi/9)*cos(14*pi/45) + sin(14*pi/45)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = sin(14*pi/45) * cos(pi/9) - sin(pi/9) * cos(14*pi/45),
{
have : sin(pi/5) = sin((14*pi/45) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = - sin(8779*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/5) (878),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_11 : -tan(4409*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = -tan(4409*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (735),
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


lemma Trigo_number_generalization_step1_12 (h0 : cos(-pi/2)≠ 0) (h1 : (1-tan(-pi/2)**2)≠ 0) : 2*tan(-pi/2)/(1 - tan(-pi/2)**2)=- tan(3*pi):=
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
have : tan(-pi) = - tan(3*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_13 : cos(pi/5) ** 2=1 - cos(4203*pi/10)**2:=
begin
have : sin(pi/5) = cos(4203*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (210),
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


lemma Trigo_number_generalization_step1_14 (h0 : cos(-2*pi)≠ 0) (h1 : (2*(cos(-3*pi/2)*cos(pi/2)+sin(-3*pi/2)*sin(pi/2)))≠ 0) (h2 : (2*(sin((-3)*pi/2)*sin(pi/2)+cos((-3)*pi/2)*cos(pi/2)))≠ 0) : sin(-2*pi)=sin(-4*pi)/(2*(cos(-3*pi/2)*cos(pi/2) + sin(-3*pi/2)*sin(pi/2))):=
begin
have : sin((-4) * pi) / (2 * (sin((-3) * pi / 2) * sin(pi / 2) + cos((-3) * pi / 2) * cos(pi / 2))) = sin(-4*pi)/(2*(cos(-3*pi/2)*cos(pi/2) + sin(-3*pi/2)*sin(pi/2))),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(-3*pi/2) * sin(pi/2) + cos(-3*pi/2) * cos(pi/2),
{
have : cos(-2*pi) = cos((-3*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_number_generalization_step1_15 : cos(-pi/7) + cos(8063*pi/9)=2 * cos(-8*pi/63) * cos(-pi/63):=
begin
have : cos(pi/9) = cos(8063*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (448),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) + cos(pi/9) = 2 * cos(-8*pi/63) * cos(-pi/63),
{
rw cos_add_cos,
have : cos(((-pi/7) + (pi/9))/2) = cos(-pi/63),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/7) - (pi/9))/2) = cos(-8*pi/63),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_16 : sin(8251*pi/18)=- cos(14462*pi/9):=
begin
have : cos(pi/9) = sin(8251*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (229),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = - cos(14462*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/9) (803),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_17 : cos(pi/2)=cos(4299*pi/2):=
begin
have : sin(1248*pi) = cos(4299*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1248*pi) (450),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(1248*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (624),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_18 (h0 : cos(3*pi/4)≠ 0) : sin(3*pi/4)/cos(3*pi/4)=- 1:=
begin
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


lemma Trigo_number_generalization_step1_19 : tan(311*pi/2)=- 1 / tan(900*pi):=
begin
have : tan(pi/2) = tan(311*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (155),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - 1 / tan(900*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (899),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_20 (h0 : cos(-3*pi/2)≠ 0) (h1 : (2*cos(-3*pi/2))≠ 0) (h2 : (2*cos((-3)*pi/2))≠ 0) : sin(-3*pi)/(2*cos(-3*pi/2))=- 4 * sin(-pi/2) ** 3 + 3 * sin(-pi/2):=
begin
have : sin((-3) * pi) / (2 * cos((-3) * pi / 2)) = sin(-3*pi)/(2*cos(-3*pi/2)),
{
field_simp at *,
},
have : sin(-3*pi/2) = sin(-3*pi) / ( 2 * cos(-3*pi/2) ),
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


lemma Trigo_number_generalization_step1_21 : cos(1607*pi/2)=0:=
begin
have : sin(pi) = cos(1607*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (402),
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


lemma Trigo_number_generalization_step1_22 : (1 - 2*sin(pi/12)**2)*cos(-pi/7)=cos(13*pi/42) / 2 + cos(pi/42) / 2:=
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


lemma Trigo_number_generalization_step1_23 : -sin(pi/2)**2 + cos(pi/2)**2=- 1:=
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
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_24 : sin(pi/3)*sin(4*pi/3) + cos(pi/3)*cos(4*pi/3)=- 1:=
begin
have : sin(4 * pi / 3) * sin(pi / 3) + cos(4 * pi / 3) * cos(pi / 3) = sin(pi/3)*sin(4*pi/3) + cos(pi/3)*cos(4*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(4*pi/3) * sin(pi/3) + cos(4*pi/3) * cos(pi/3),
{
have : cos(pi) = cos((4*pi/3) - (pi/3)),
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


lemma Trigo_number_generalization_step1_25 : cos(-pi/6) ** 2=cos(-pi/3)/2 + 1/2:=
begin
have : 1 - (1 / 2 - cos(-pi / 3) / 2) = cos(-pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : cos(-pi/6) ** 2 = 1 - sin(-pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_26 : cos(6628*pi/7)=sin(-pi/7) * cos(pi/2) - sin(pi/2) * cos(-pi/7):=
begin
have : sin(-9*pi/14) = cos(6628*pi/7),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-9*pi/14) (473),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-9*pi/14) = sin(-pi/7) * cos(pi/2) - sin(pi/2) * cos(-pi/7),
{
have : sin(-9*pi/14) = sin((-pi/7) - (pi/2)),
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


lemma Trigo_number_generalization_step1_27 : tan(515*pi/4)=- 1:=
begin
have : tan(3*pi/4) = tan(515*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (3*pi/4) (128),
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


lemma Trigo_number_generalization_step1_28 (h0 : cos(pi/7)≠ 0) (h1 : (2*cos(pi/7))≠ 0) : sin(2*pi/7)/(2*cos(pi/7))=- sin(12571*pi/7):=
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
have : sin(pi/7) = - sin(12571*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/7) (898),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_29 : sin(2*pi)*cos(-7*pi/2) + sin(-7*pi/2)*cos(2*pi)=- 4 * sin(-pi/2) ** 3 + 3 * sin(-pi/2):=
begin
have : sin((-7) * pi / 2) * cos(2 * pi) + sin(2 * pi) * cos((-7) * pi / 2) = sin(2*pi)*cos(-7*pi/2) + sin(-7*pi/2)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2) = sin(-7*pi/2) * cos(2*pi) + sin(2*pi) * cos(-7*pi/2),
{
have : sin(-3*pi/2) = sin((-7*pi/2) + (2*pi)),
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


lemma Trigo_number_generalization_step1_30 : cos(3421*pi/2)=0:=
begin
have : cos(pi/2) = cos(3421*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (855),
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


lemma Trigo_number_generalization_step1_31 : -sin(1999*pi/6)=1 / 2:=
begin
have : cos(pi/3) = -sin(1999*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (166),
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


lemma Trigo_number_generalization_step1_32 : sin(pi/7) * sin(pi)=cos(-6*pi/7)/2 - cos(4*pi/7)**2 + 1/2:=
begin
have : cos((-6) * pi / 7) / 2 - (2 * cos(4 * pi / 7) ** 2 - 1) / 2 = cos(-6*pi/7)/2 - cos(4*pi/7)**2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(8*pi/7) = 2 * cos(4*pi/7) ** 2 - 1,
{
have : cos(8*pi/7) = cos(2*(4*pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) * sin(pi) = cos(-6*pi/7) / 2 - cos(8*pi/7) / 2,
{
rw sin_mul_sin,
have : cos((pi/7) + (pi)) = cos(8*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/7) - (pi)) = cos(-6*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_33 : sin(7*pi/8)*cos(-pi/8) + sin(-pi/8)*cos(7*pi/8)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(7*pi/8) * cos(-pi/8) + sin(-pi/8) * cos(7*pi/8),
{
have : sin(3*pi/4) = sin((7*pi/8) + (-pi/8)),
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


lemma Trigo_number_generalization_step1_34 : cos(1629*pi/2)=sin(819*pi):=
begin
have : sin(-2*pi) = cos(1629*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (406),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(819*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (408),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_35 : -sin(5045*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -sin(5045*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (630),
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


lemma Trigo_number_generalization_step1_36 : cos(-pi/3)=4*sin(11255*pi/18)**3 - 3*sin(11255*pi/18):=
begin
have : -((-4) * sin(11255 * pi / 18) ** 3 + 3 * sin(11255 * pi / 18)) = 4*sin(11255*pi/18)**3 - 3*sin(11255*pi/18),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(11255*pi/6) = -4 * sin(11255*pi/18) ** 3 + 3 * sin(11255*pi/18),
{
have : sin(11255*pi/6) = sin(3*(11255*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(11255*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (937),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_37 : -4*sin(pi/12)**3 + 3*sin(pi/12)=sqrt( 2 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_38 : sin(6389*pi/6)=sin(5393*pi/6):=
begin
have : cos(pi/3) = sin(6389*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (532),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(5393*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (449),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_39 : cos(785*pi/2)=0:=
begin
have : cos(pi/2) = cos(785*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (196),
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


lemma Trigo_number_generalization_step1_40 : sin(7183*pi/7)=sin(8014*pi/7):=
begin
have : sin(pi/7) = sin(7183*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/7) (513),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(8014*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/7) (572),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_41 : cos(-pi/6) - cos(pi/8)=-cos(-pi/8) + cos(-pi/6):=
begin
have : (-2) * (cos(-pi / 8) / 2 - cos(-pi / 6) / 2) = -cos(-pi/8) + cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-7*pi/48) * sin(-pi/48) = cos(-pi/8) / 2 - cos(-pi/6) / 2,
{
rw sin_mul_sin,
have : cos((-7*pi/48) + (-pi/48)) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-7*pi/48) - (-pi/48)) = cos(-pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -2*(sin(-7*pi/48) * sin(-pi/48)) = -2*sin(-7*pi/48)*sin(-pi/48),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-pi/6) - cos(pi/8) = - 2 * sin(-7*pi/48) * sin(-pi/48),
{
rw cos_sub_cos,
have : sin(((-pi/6) + (pi/8))/2) = sin(-pi/48),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (pi/8))/2) = sin(-7*pi/48),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_42 : sin(0)=-sin(1300*pi)*cos(2*pi) + sin(2*pi)*cos(-2*pi):=
begin
have : -sin(1300 * pi) * cos(2 * pi) + sin(2 * pi) * cos((-2) * pi) = -sin(1300*pi)*cos(2*pi) + sin(2*pi)*cos(-2*pi),
{
field_simp at *,
},
have : sin(-2*pi) = -sin(1300*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (649),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(0) = sin(-2*pi) * cos(2*pi) + sin(2*pi) * cos(-2*pi),
{
have : sin(0) = sin((-2*pi) + (2*pi)),
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


lemma Trigo_number_generalization_step1_43 (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : sin(2*pi)/(2*cos(pi))=0:=
begin
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


lemma Trigo_number_generalization_step1_44 : -cos(442*pi)=cos(843*pi):=
begin
have : cos(pi) = -cos(442*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (221),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(843*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (421),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_45 : cos(0)*cos(pi) + sin(0)*sin(pi) + cos(pi/3)=2 * cos(2*pi/3) * cos(-pi/3):=
begin
have : cos(pi / 3) + (sin(0) * sin(pi) + cos(0) * cos(pi)) = cos(0)*cos(pi) + sin(0)*sin(pi) + cos(pi/3),
{
field_simp at *,
ring,
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


lemma Trigo_number_generalization_step1_46 : -3*sin(pi/12) + 4*sin(pi/12)**3 + sin(pi/6)=2 * sin(-pi/24) * cos(5*pi/24):=
begin
have : sin(pi / 6) - ((-4) * sin(pi / 12) ** 3 + 3 * sin(pi / 12)) = -3*sin(pi/12) + 4*sin(pi/12)**3 + sin(pi/6),
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
have : sin(pi/6) - sin(pi/4) = 2 * sin(-pi/24) * cos(5*pi/24),
{
rw sin_sub_sin,
have : cos(((pi/6) + (pi/4))/2) = cos(5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (pi/4))/2) = sin(-pi/24),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_47 : -1 + 2*cos(pi/6)**2=1 / 2:=
begin
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


lemma Trigo_number_generalization_step1_48 : -sin(968*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(968*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (161),
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


lemma Trigo_number_generalization_step1_49 (h0 : cos(2*pi)≠ 0) : tan(2*pi)=(sin(-pi/3)*cos(7*pi/3) + sin(7*pi/3)*cos(-pi/3))/cos(2*pi):=
begin
have : (sin(7 * pi / 3) * cos(-pi / 3) + sin(-pi / 3) * cos(7 * pi / 3)) / cos(2 * pi) = (sin(-pi/3)*cos(7*pi/3) + sin(7*pi/3)*cos(-pi/3))/cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(2*pi) = sin(2*pi) / cos(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_50 (h0 : cos((pi/2)/2)≠ 0) (h1 : sin(pi/2)≠ 0) : (1 - cos(pi/2))/sin(pi/2)=1:=
begin
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


lemma Trigo_number_generalization_step1_51 : sin(5531*pi/3)=- sin(787*pi/3):=
begin
have : sin(-pi/3) = sin(5531*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (922),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(787*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (131),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_52 : sin(812*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(812*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (135),
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


lemma Trigo_number_generalization_step1_53 : sin(41*pi/42)*cos(-pi/7) + sin(-pi/7)*cos(41*pi/42)=1 / 2:=
begin
have : sin(5*pi/6) = sin(41*pi/42) * cos(-pi/7) + sin(-pi/7) * cos(41*pi/42),
{
have : sin(5*pi/6) = sin((41*pi/42) + (-pi/7)),
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


lemma Trigo_number_generalization_step1_54 : -sin(3459*pi/2)=4 * cos(-2*pi) ** 3 - 3 * cos(-2*pi):=
begin
have : cos(-6*pi) = -sin(3459*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-6*pi) (867),
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


lemma Trigo_number_generalization_step1_55 : tan(4933*pi/9)=tan(5140*pi/9):=
begin
have : tan(pi/9) = tan(4933*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (548),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = tan(5140*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (571),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_56 (h0 : tan(3501*pi/4)≠ 0) : -1/tan(3501*pi/4)=- 1:=
begin
have : (-1) / tan(3501 * pi / 4) = -1/tan(3501*pi/4),
{
field_simp at *,
},
have : tan(3*pi/4) = -1 / tan(3501*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (3*pi/4) (874),
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


lemma Trigo_number_generalization_step1_57 : cos(-pi)=-cos(1806*pi):=
begin
have : sin(3531*pi/2) = -cos(1806*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3531*pi/2) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(3531*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (883),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_58 : cos(-pi/6) + cos(1494*pi)=2 * cos(13*pi/12) * cos(11*pi/12):=
begin
have : cos(1494 * pi) + cos(-pi / 6) = cos(-pi/6) + cos(1494*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(1494*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (746),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) + cos(-pi/6) = 2 * cos(13*pi/12) * cos(11*pi/12),
{
rw cos_add_cos,
have : cos(((2*pi) + (-pi/6))/2) = cos(11*pi/12),
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_59 (h0 : sin(pi/4)≠ 0) (h1 : (2*sin(pi/4))≠ 0) : cos(pi/4)=cos(604*pi)/(2*sin(pi/4)):=
begin
have : sin(pi/2) = cos(604*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (302),
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


lemma Trigo_number_generalization_step1_60 : -sin(pi/2)*sin(1603*pi/2)=- sin(-5*pi/2) / 2 + sin(-3*pi/2) / 2:=
begin
have : sin(pi / 2) * -sin(1603 * pi / 2) = -sin(pi/2)*sin(1603*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(1603*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (401),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(-2*pi) = - sin(-5*pi/2) / 2 + sin(-3*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-2*pi) + (pi/2)) = sin(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi/2)) = sin(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_61 : sin(pi/2) / cos(pi/2)=tan(1997*pi/2):=
begin
have : tan(pi/2) = tan(1997*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (998),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) / cos(pi/2) = tan(pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_62 : -sin(1451*pi/10)=2 * cos(-pi/5) ** 2 - 1:=
begin
have : cos(-2*pi/5) = -sin(1451*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/5) (72),
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


lemma Trigo_number_generalization_step1_63 (h0 : sin(-8*pi/7)≠ 0) (h1 : (4*sin(-8*pi/7))≠ 0) (h2 : (2*sin((-8)*pi/7))≠ 0) : sin(-pi/7) * sin(pi)=sin(-16*pi/7)/(4*sin(-8*pi/7)) - cos(6*pi/7)/2:=
begin
have : sin((-16) * pi / 7) / (2 * sin((-8) * pi / 7)) / 2 - cos(6 * pi / 7) / 2 = sin(-16*pi/7)/(4*sin(-8*pi/7)) - cos(6*pi/7)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-8*pi/7) = sin(-16*pi/7) / ( 2 * sin(-8*pi/7) ),
{
have : sin(-16*pi/7) = sin(2*(-8*pi/7)),
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
have : sin(-pi/7) * sin(pi) = cos(-8*pi/7) / 2 - cos(6*pi/7) / 2,
{
rw sin_mul_sin,
have : cos((-pi/7) + (pi)) = cos(6*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/7) - (pi)) = cos(-8*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_64 (h0 : cos((4*pi)/2)≠ 0) (h1 : (1+cos(4*pi))≠ 0) : sin(4*pi)/(1 + cos(4*pi))=- 1 / tan(377*pi/2):=
begin
have : tan(2*pi) = sin(4*pi) / ( 1 + cos(4*pi) ),
{
have : tan(2*pi) = tan((4*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - 1 / tan(377*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi) (186),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_65 (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : sin(2*pi)/(2*cos(pi))=- cos(3245*pi/2):=
begin
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
have : sin(pi) = - cos(3245*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (811),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_66 : -sin(-pi/7)*cos(6*pi/7) + sin(pi/8) + sin(6*pi/7)*cos(-pi/7)=2 * sin(9*pi/16) * cos(-7*pi/16):=
begin
have : sin(pi / 8) + (sin(6 * pi / 7) * cos(-pi / 7) - sin(-pi / 7) * cos(6 * pi / 7)) = -sin(-pi/7)*cos(6*pi/7) + sin(pi/8) + sin(6*pi/7)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(6*pi/7) * cos(-pi/7) - sin(-pi/7) * cos(6*pi/7),
{
have : sin(pi) = sin((6*pi/7) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) + sin(pi) = 2 * sin(9*pi/16) * cos(-7*pi/16),
{
rw sin_add_sin,
have : sin(((pi/8) + (pi))/2) = sin(9*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/8) - (pi))/2) = cos(-7*pi/16),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_67 : sin(2689*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = sin(2689*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (112),
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


lemma Trigo_number_generalization_step1_68 : -sin(7664*pi/5)=- cos(523*pi/10):=
begin
have : sin(-pi/5) = -sin(7664*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/5) (766),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = - cos(523*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/5) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_69 : -4*sin(5*pi/18)**3 + 3*sin(5*pi/18)=1 / 2:=
begin
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


lemma Trigo_number_generalization_step1_70 : -cos(13892*pi/7)=4 * cos(pi/7) ** 3 - 3 * cos(pi/7):=
begin
have : cos(3*pi/7) = -cos(13892*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/7) (992),
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


lemma Trigo_number_generalization_step1_71 : cos(pi/4)=1 - 2*(sin(-2*pi)*cos(17*pi/8) + sin(17*pi/8)*cos(-2*pi))**2:=
begin
have : 1 - 2 * (sin(17 * pi / 8) * cos((-2) * pi) + sin((-2) * pi) * cos(17 * pi / 8)) ** 2 = 1 - 2*(sin(-2*pi)*cos(17*pi/8) + sin(17*pi/8)*cos(-2*pi))**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) = sin(17*pi/8) * cos(-2*pi) + sin(-2*pi) * cos(17*pi/8),
{
have : sin(pi/8) = sin((17*pi/8) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step1_72 : cos(315*pi)=- sin(3237*pi/2):=
begin
have : cos(pi) = cos(315*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (157),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - sin(3237*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (808),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_73 : sin(2896*pi/5)=cos(16533*pi/10):=
begin
have : sin(-pi/5) = sin(2896*pi/5),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/5) (289),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = cos(16533*pi/10),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (826),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_74 : cos(11261*pi/14)**2=1 - cos(pi/7) ** 2:=
begin
have : sin(pi/7) = cos(11261*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/7) (402),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) ** 2 = 1 - cos(pi/7) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_75 : cos(-pi/4)=1 - 2*cos(8061*pi/8)**2:=
begin
have : 1 - 2 * (-cos(8061 * pi / 8)) ** 2 = 1 - 2*cos(8061*pi/8)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) = -cos(8061*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (503),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step1_76 (h0 : tan(1544*pi/3)≠ 0) : -1/tan(1544*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(1544 * pi / 3) = -1/tan(1544*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1544*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (514),
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


lemma Trigo_number_generalization_step1_77 : cos(-pi/2)=-sin(3665*pi/4)**2 + cos(-pi/4)**2:=
begin
have : -(-sin(3665 * pi / 4)) ** 2 + cos(-pi / 4) ** 2 = -sin(3665*pi/4)**2 + cos(-pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) = -sin(3665*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (458),
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


lemma Trigo_number_generalization_step1_78 : (-3*cos(-pi/9) + 4*cos(-pi/9)**3)*sin(pi/8)=sin(11*pi/24) / 2 + sin(-5*pi/24) / 2:=
begin
have : sin(pi / 8) * (4 * cos(-pi / 9) ** 3 - 3 * cos(-pi / 9)) = (-3*cos(-pi/9) + 4*cos(-pi/9)**3)*sin(pi/8),
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
have : sin(pi/8) * cos(-pi/3) = sin(11*pi/24) / 2 + sin(-5*pi/24) / 2,
{
rw sin_mul_cos,
have : sin((pi/8) + (-pi/3)) = sin(-5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (-pi/3)) = sin(11*pi/24),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_79 : 2*sin(-pi/16)*cos(-pi/7)*cos(-pi/16)=sin(pi/56) / 2 + sin(-15*pi/56) / 2:=
begin
have : 2 * sin(-pi / 16) * cos(-pi / 16) * cos(-pi / 7) = 2*sin(-pi/16)*cos(-pi/7)*cos(-pi/16),
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
have : sin(-pi/8) * cos(-pi/7) = sin(pi/56) / 2 + sin(-15*pi/56) / 2,
{
rw sin_mul_cos,
have : sin((-pi/8) + (-pi/7)) = sin(-15*pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/8) - (-pi/7)) = sin(pi/56),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_80 : sin(10399*pi/6)=- sin(5365*pi/6):=
begin
have : sin(-pi/6) = sin(10399*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (866),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(5365*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (447),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_81 (h0 : cos((4*pi/3)/2)≠ 0) (h1 : (1+cos(4*pi/3))≠ 0) (h2 : (cos(4*pi/3)+1)≠ 0) : sin(4*pi/3)/(cos(4*pi/3) + 1)=- sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_82 (h0 : cos(-pi/2)≠ 0) (h1 : (2*cos(-pi/2))≠ 0) : cos(-7*pi/18)=cos(-pi/2)*cos(pi/9) - sin(-pi)*sin(pi/9)/(2*cos(-pi/2)):=
begin
have : -sin(pi / 9) * (sin(-pi) / (2 * cos(-pi / 2))) + cos(pi / 9) * cos(-pi / 2) = cos(-pi/2)*cos(pi/9) - sin(-pi)*sin(pi/9)/(2*cos(-pi/2)),
{
field_simp at *,
ring,
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
have : cos(-7*pi/18) = - sin(pi/9) * sin(-pi/2) + cos(pi/9) * cos(-pi/2),
{
have : cos(-7*pi/18) = cos((pi/9) + (-pi/2)),
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


lemma Trigo_number_generalization_step1_83 : cos(-2*pi/7)=1 - 2*sin(-pi/7)**2:=
begin
have : -sin(-pi / 7) ** 2 + (1 - sin(-pi / 7) ** 2) = 1 - 2*sin(-pi/7)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/7) ** 2 = 1 - sin(-pi/7) ** 2,
{
rw cos_sq',
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


lemma Trigo_number_generalization_step1_84 : -tan(1655*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = -tan(1655*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (276),
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


lemma Trigo_number_generalization_step1_85 : sin(-5*pi/18)*sin(-pi/6) + cos(-5*pi/18)*cos(-pi/6) + cos(-pi/5)=2 * cos(2*pi/45) * cos(-7*pi/45):=
begin
have : sin((-5) * pi / 18) * sin(-pi / 6) + cos((-5) * pi / 18) * cos(-pi / 6) + cos(-pi / 5) = sin(-5*pi/18)*sin(-pi/6) + cos(-5*pi/18)*cos(-pi/6) + cos(-pi/5),
{
field_simp at *,
},
have : cos(-pi/9) = sin(-5*pi/18) * sin(-pi/6) + cos(-5*pi/18) * cos(-pi/6),
{
have : cos(-pi/9) = cos((-5*pi/18) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) + cos(-pi/5) = 2 * cos(2*pi/45) * cos(-7*pi/45),
{
rw cos_add_cos,
have : cos(((-pi/9) + (-pi/5))/2) = cos(-7*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (-pi/5))/2) = cos(2*pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_86 : -1 + 2*cos(3*pi/8)**2=- sqrt( 2 ) / 2:=
begin
have : 2 * cos(3 * pi / 8) ** 2 - 1 = -1 + 2*cos(3*pi/8)**2,
{
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


lemma Trigo_number_generalization_step1_87 : -sin(-pi/16)**2 + cos(-pi/16)**2=- cos(5417*pi/8):=
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
have : cos(-pi/8) = - cos(5417*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/8) (338),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_88 : -sin(pi/6)**2 + cos(pi/6)**2=1 / 2:=
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_89 (h0 : cos((pi/2)/2)≠ 0) (h1 : (cos(pi/2)+1)≠ 0) (h2 : (1+cos(pi/2))≠ 0) : sin(pi/2)/(cos(pi/2) + 1)=1:=
begin
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


lemma Trigo_number_generalization_step1_90 : sin(1987*pi/2)=- 1:=
begin
have : cos(pi) = sin(1987*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (496),
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


lemma Trigo_number_generalization_step1_91 : sin(pi/4) ** 2=1/2 - cos(721*pi/2)/2:=
begin
have : cos(pi/2) = cos(721*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (180),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_92 : sin(19721*pi/14)*cos(pi/8)=cos(15*pi/56) / 2 + cos(-pi/56) / 2:=
begin
have : cos(pi / 8) * sin(19721 * pi / 14) = sin(19721*pi/14)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = sin(19721*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (704),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) * cos(-pi/7) = cos(15*pi/56) / 2 + cos(-pi/56) / 2,
{
rw cos_mul_cos,
have : cos((pi/8) + (-pi/7)) = cos(-pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/8) - (-pi/7)) = cos(15*pi/56),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_93 : sin(pi/3)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi/3)=sin(3295*pi/2):=
begin
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
have : sin(-pi/2) = sin(3295*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (823),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_94 : -cos(10735*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -cos(10735*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (894),
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


lemma Trigo_number_generalization_step1_95 (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : sin(2*pi/3)/(2*cos(pi/3))=sqrt( 3 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_96 : -sin(6899*pi/6) + cos(pi/3)=2 * cos(pi/3) * cos(0):=
begin
have : cos(pi / 3) + -sin(6899 * pi / 6) = -sin(6899*pi/6) + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(6899*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (574),
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


lemma Trigo_number_generalization_step1_97 : sin(7511*pi/5)=sin(3901*pi/5):=
begin
have : sin(pi/5) = sin(7511*pi/5),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/5) (751),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = sin(3901*pi/5),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/5) (390),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_98 : sin(-pi/7)=-cos(15181*pi/28)**2 + sin(15181*pi/28)**2:=
begin
have : -(-sin(15181 * pi / 28) ** 2 + cos(15181 * pi / 28) ** 2) = -cos(15181*pi/28)**2 + sin(15181*pi/28)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(15181*pi/14) = -sin(15181*pi/28) ** 2 + cos(15181*pi/28) ** 2,
{
have : cos(15181*pi/14) = cos(2*(15181*pi/28)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) = - cos(15181*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/7) (542),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_99 : cos(5917*pi/3)**2 + cos(-pi/6)**2=1:=
begin
have : (-cos(5917 * pi / 3)) ** 2 + cos(-pi / 6) ** 2 = cos(5917*pi/3)**2 + cos(-pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(5917*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (986),
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


lemma Trigo_number_generalization_step1_100 : -sin(-2*pi)*sin(13*pi/6) + cos(-2*pi)*cos(13*pi/6)=sqrt( 3 ) / 2:=
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


lemma Trigo_number_generalization_step1_101 : sin(11*pi/4)*cos(pi) - sin(pi)*cos(11*pi/4)=sin(2*pi) * cos(pi/4) - sin(pi/4) * cos(2*pi):=
begin
have : sin(7*pi/4) = sin(11*pi/4) * cos(pi) - sin(pi) * cos(11*pi/4),
{
have : sin(7*pi/4) = sin((11*pi/4) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/4) = sin(2*pi) * cos(pi/4) - sin(pi/4) * cos(2*pi),
{
have : sin(7*pi/4) = sin((2*pi) - (pi/4)),
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


lemma Trigo_number_generalization_step1_102 : sin(-15*pi/8)=sin(-2*pi)*cos(pi/8) + (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(pi/8):=
begin
have : sin(pi / 8) * (4 * cos((-2) * pi / 3) ** 3 - 3 * cos((-2) * pi / 3)) + sin((-2) * pi) * cos(pi / 8) = sin(-2*pi)*cos(pi/8) + (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(pi/8),
{
field_simp at *,
ring,
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
have : sin(-15*pi/8) = sin(pi/8) * cos(-2*pi) + sin(-2*pi) * cos(pi/8),
{
have : sin(-15*pi/8) = sin((pi/8) + (-2*pi)),
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


lemma Trigo_number_generalization_step1_103 : cos(6231*pi/7)**2=cos(2*pi/7) / 2 + 1 / 2:=
begin
have : cos(pi/7) = cos(6231*pi/7),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/7) (445),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) ** 2 = cos(2*pi/7) / 2 + 1 / 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
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


lemma Trigo_number_generalization_step1_104 : -sin(pi/12)**2 + cos(pi/12)**2=sqrt( 3 ) / 2:=
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_105 (h0 : cos((4*pi/3)/2)≠ 0) (h1 : sin(4*pi/3)≠ 0) : (1 - cos(4*pi/3))/sin(4*pi/3)=- sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_106 : -sin(2503*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = -sin(2503*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/6) (209),
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


lemma Trigo_number_generalization_step1_107 : -tan(557*pi/4)=- 1:=
begin
have : tan(3*pi/4) = -tan(557*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (140),
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


lemma Trigo_number_generalization_step1_108 : -cos(16102*pi/9)=cos(125*pi/9):=
begin
have : cos(pi/9) = -cos(16102*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/9) (894),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = cos(125*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_109 : -sin(-pi/10)**2 + cos(-pi/10)**2=sin(5583*pi/10):=
begin
have : cos(-pi/5) = -sin(-pi/10) ** 2 + cos(-pi/10) ** 2,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = sin(5583*pi/10),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/5) (279),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_110 (h0 : cos(-2*pi)≠ 0) (h1 : (2*cos((-2)*pi))≠ 0) (h2 : (2*cos(-2*pi))≠ 0) : sin(-4*pi)/(2*cos(-2*pi))=- cos(3291*pi/2):=
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
have : sin(-2*pi) = - cos(3291*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (821),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_111 : 2*sin(pi/6)*cos(pi/6)=sqrt( 3 ) / 2:=
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
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_112 : cos(1519*pi/2)=- sin(-pi/2) * sin(-pi) + cos(-pi/2) * cos(-pi):=
begin
have : cos(-3*pi/2) = cos(1519*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-3*pi/2) (379),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_number_generalization_step1_113 : -sin(2708*pi/9)=- sin(15056*pi/9):=
begin
have : sin(-pi/9) = -sin(2708*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (150),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = - sin(15056*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (836),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_114 : -3*cos(pi/6) + 4*cos(pi/6)**3=cos(3175*pi/2):=
begin
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
have : cos(pi/2) = cos(3175*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (794),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_115 (h0 : sin(pi/2)≠ 0) : sin(-pi/6)*sin(pi/3) + cos(-pi/6)*cos(pi/3)=sin(pi) / ( 2 * sin(pi/2) ):=
begin
have : sin(pi / 3) * sin(-pi / 6) + cos(pi / 3) * cos(-pi / 6) = sin(-pi/6)*sin(pi/3) + cos(-pi/6)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(pi/3) * sin(-pi/6) + cos(pi/3) * cos(-pi/6),
{
have : cos(pi/2) = cos((pi/3) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_number_generalization_step1_116 : -3*cos(pi/36) + 4*cos(pi/36)**3=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
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


lemma Trigo_number_generalization_step1_117 (h0 : tan(6287*pi/10)≠ 0) : 1/tan(6287*pi/10)=- 1 / tan(9073*pi/10):=
begin
have : tan(-pi/5) = 1 / tan(6287*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/5) (628),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = - 1 / tan(9073*pi/10),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/5) (907),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_118 : -sin(5890*pi/3)=- sin(4990*pi/3):=
begin
have : sin(pi/3) = -sin(5890*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (981),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(4990*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (831),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_119 : cos(pi/3)=-2*sin(8795*pi/12)*cos(8795*pi/12):=
begin
have : -(2 * sin(8795 * pi / 12) * cos(8795 * pi / 12)) = -2*sin(8795*pi/12)*cos(8795*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(8795*pi/6) = 2 * sin(8795*pi/12) * cos(8795*pi/12),
{
have : sin(8795*pi/6) = sin(2*(8795*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = - sin(8795*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (732),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_120 : sin(-pi/7)*sin(-5*pi/84) + cos(-pi/7)*cos(-5*pi/84)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin((-5) * pi / 84) * sin(-pi / 7) + cos((-5) * pi / 84) * cos(-pi / 7) = sin(-pi/7)*sin(-5*pi/84) + cos(-pi/7)*cos(-5*pi/84),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(-5*pi/84) * sin(-pi/7) + cos(-5*pi/84) * cos(-pi/7),
{
have : cos(pi/12) = cos((-5*pi/84) - (-pi/7)),
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


lemma Trigo_number_generalization_step1_121 : cos(27539*pi/18)=- sin(pi/6) * sin(-pi/9) + cos(pi/6) * cos(-pi/9):=
begin
have : cos(pi/18) = cos(27539*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/18) (765),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = - sin(pi/6) * sin(-pi/9) + cos(pi/6) * cos(-pi/9),
{
have : cos(pi/18) = cos((pi/6) + (-pi/9)),
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


lemma Trigo_number_generalization_step1_122 : -tan(5231*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = -tan(5231*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (872),
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


lemma Trigo_number_generalization_step1_123 : -cos(634*pi/3)=1 / 2:=
begin
have : sin(pi/6) = -cos(634*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (105),
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


lemma Trigo_number_generalization_step1_124 : cos(2017*pi/6)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = cos(2017*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (168),
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


lemma Trigo_number_generalization_step1_125 : sin(pi/3) ** 2=1/2 - cos(5132*pi/3)/2:=
begin
have : cos(2*pi/3) = cos(5132*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (855),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step1_126 (h0 : cos(10*pi/9)≠ 0) (h1 : cos(pi/9)≠ 0) (h2 : (tan(pi/9)*tan(10*pi/9)+1)≠ 0) (h3 : (1+tan(10*pi/9)*tan(pi/9))≠ 0) : (-tan(pi/9) + tan(10*pi/9))/(tan(pi/9)*tan(10*pi/9) + 1)=0:=
begin
have : (tan(10 * pi / 9) - tan(pi / 9)) / (1 + tan(10 * pi / 9) * tan(pi / 9)) = (-tan(pi/9) + tan(10*pi/9))/(tan(pi/9)*tan(10*pi/9) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(10*pi/9) - tan(pi/9) ) / ( 1 + tan(10*pi/9) * tan(pi/9) ),
{
have : tan(pi) = tan((10*pi/9) - (pi/9)),
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


lemma Trigo_number_generalization_step1_127 : sin(5746*pi/3)=sin(976*pi/3):=
begin
have : sin(-pi/3) = sin(5746*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (957),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(976*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (162),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_128 : sin(pi/8)*cos(3*pi/8) + sin(3*pi/8)*cos(pi/8)=1:=
begin
have : sin(3 * pi / 8) * cos(pi / 8) + sin(pi / 8) * cos(3 * pi / 8) = sin(pi/8)*cos(3*pi/8) + sin(3*pi/8)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(3*pi/8) * cos(pi/8) + sin(pi/8) * cos(3*pi/8),
{
have : sin(pi/2) = sin((3*pi/8) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step1_129 (h0 : cos((3*pi/2)/2)≠ 0) (h1 : sin(3*pi/2)≠ 0) : (1 - cos(3*pi/2))/sin(3*pi/2)=- 1:=
begin
have : tan(3*pi/4) = ( 1 - cos(3*pi/2) ) / sin(3*pi/2),
{
have : tan(3*pi/4) = tan((3*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = - 1,
{
rw tan_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_130 : sin(-pi/3)=3*cos(2857*pi/18) - 4*cos(2857*pi/18)**3:=
begin
have : -(4 * cos(2857 * pi / 18) ** 3 - 3 * cos(2857 * pi / 18)) = 3*cos(2857*pi/18) - 4*cos(2857*pi/18)**3,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2857*pi/6) = 4 * cos(2857*pi/18) ** 3 - 3 * cos(2857*pi/18),
{
have : cos(2857*pi/6) = cos(3*(2857*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = - cos(2857*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (238),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_131 (h0 : cos((pi/6)/2)≠ 0) (h1 : (1+cos(pi/6))≠ 0) (h2 : (cos(pi/6)+1)≠ 0) : sin(pi/6)/(cos(pi/6) + 1)=2 - sqrt( 3 ):=
begin
have : sin(pi / 6) / (1 + cos(pi / 6)) = sin(pi/6)/(cos(pi/6) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = sin(pi/6) / ( 1 + cos(pi/6) ),
{
have : tan(pi/12) = tan((pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 2 - sqrt( 3 ),
{
rw tan_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step1_132 : cos(2*pi) + cos(pi/2)=cos(pi/2) + cos(2*pi):=
begin
have : 2 * (cos(pi / 2) / 2 + cos(2 * pi) / 2) = cos(pi/2) + cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/4) * cos(3*pi/4) = cos(pi/2) / 2 + cos(2*pi) / 2,
{
rw cos_mul_cos,
have : cos((5*pi/4) + (3*pi/4)) = cos(2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/4) - (3*pi/4)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(cos(5*pi/4) * cos(3*pi/4)) = 2*cos(3*pi/4)*cos(5*pi/4),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(2*pi) + cos(pi/2) = 2 * cos(3*pi/4) * cos(5*pi/4),
{
rw cos_add_cos,
have : cos(((2*pi) + (pi/2))/2) = cos(5*pi/4),
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_133 : cos(-2*pi/3)=1 - 2*cos(1933*pi/6)**2:=
begin
have : 1 - 2 * (-cos(1933 * pi / 6)) ** 2 = 1 - 2*cos(1933*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = -cos(1933*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (161),
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


lemma Trigo_number_generalization_step1_134 : sin(-pi/7) - sin(pi)=-2*sin(-4*pi/7)*sin(1455*pi/14):=
begin
have : 2 * sin((-4) * pi / 7) * -sin(1455 * pi / 14) = -2*sin(-4*pi/7)*sin(1455*pi/14),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/7) = -sin(1455*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/7) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) - sin(pi) = 2 * sin(-4*pi/7) * cos(3*pi/7),
{
rw sin_sub_sin,
have : cos(((-pi/7) + (pi))/2) = cos(3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/7) - (pi))/2) = sin(-4*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_135 : -sin(4987*pi/8)=- cos(5303*pi/8):=
begin
have : cos(-pi/8) = -sin(4987*pi/8),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (311),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = - cos(5303*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/8) (331),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_136 : sin(-2*pi)=-1 + 2*cos(407*pi/4)**2:=
begin
have : 2 * cos(407 * pi / 4) ** 2 - 1 = -1 + 2*cos(407*pi/4)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(407*pi/2) = 2 * cos(407*pi/4) ** 2 - 1,
{
have : cos(407*pi/2) = cos(2*(407*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = cos(407*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (102),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_137 : -cos(pi/6) - sin(8639*pi/6)=- 2 * sin(-pi/4) * sin(-pi/12):=
begin
have : -sin(8639 * pi / 6) - cos(pi / 6) = -cos(pi/6) - sin(8639*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(8639*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (719),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) - cos(pi/6) = - 2 * sin(-pi/4) * sin(-pi/12),
{
rw cos_sub_cos,
have : sin(((-pi/3) + (pi/6))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (pi/6))/2) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_138 : cos(2353*pi/3)=1 / 2:=
begin
have : sin(5*pi/6) = cos(2353*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (391),
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


lemma Trigo_number_generalization_step1_139 : cos(461*pi/3) + cos(-2*pi)=2 * cos(-7*pi/6) * cos(-5*pi/6):=
begin
have : cos((-2) * pi) + cos(461 * pi / 3) = cos(461*pi/3) + cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(461*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (77),
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


lemma Trigo_number_generalization_step1_140 : cos(2605*pi/3)=1 / 2:=
begin
have : sin(pi/6) = cos(2605*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (434),
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


lemma Trigo_number_generalization_step1_141 : sin(-2*pi/3)*cos(-pi/6) - sin(-pi/6)*cos(-2*pi/3)=- sin(1685*pi/2):=
begin
have : sin((-2) * pi / 3) * cos(-pi / 6) - sin(-pi / 6) * cos((-2) * pi / 3) = sin(-2*pi/3)*cos(-pi/6) - sin(-pi/6)*cos(-2*pi/3),
{
field_simp at *,
},
have : sin(-pi/2) = sin(-2*pi/3) * cos(-pi/6) - sin(-pi/6) * cos(-2*pi/3),
{
have : sin(-pi/2) = sin((-2*pi/3) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(1685*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (421),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_142 : sin(-pi/3)*cos(pi/2) + sin(pi/2)*cos(-pi/3)=1 / 2:=
begin
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


lemma Trigo_number_generalization_step1_143 : -cos(6667*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -cos(6667*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (555),
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


lemma Trigo_number_generalization_step1_144 : sin(pi/7)*cos(11*pi/21) + sin(11*pi/21)*cos(pi/7)=sqrt( 3 ) / 2:=
begin
have : sin(11 * pi / 21) * cos(pi / 7) + sin(pi / 7) * cos(11 * pi / 21) = sin(pi/7)*cos(11*pi/21) + sin(11*pi/21)*cos(pi/7),
{
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
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_145 : sin(0)*sin(2*pi) + cos(0)*cos(2*pi)=cos(1978*pi):=
begin
have : cos(-2*pi) = sin(0) * sin(2*pi) + cos(0) * cos(2*pi),
{
have : cos(-2*pi) = cos((0) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(1978*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (988),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_146 : -1 + 2*cos(pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : 2 * cos(pi / 24) ** 2 - 1 = -1 + 2*cos(pi/24)**2,
{
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


lemma Trigo_number_generalization_step1_147 : cos(-pi/4) ** 2=1 - cos(3863*pi/4)**2:=
begin
have : 1 - (-cos(3863 * pi / 4)) ** 2 = 1 - cos(3863*pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) = -cos(3863*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (482),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) ** 2 = 1 - sin(-pi/4) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_148 : cos(-pi/3)*cos(13*pi/12) - sin(-pi/3)*sin(13*pi/12)=- sqrt( 2 ) / 2:=
begin
have : -sin(13 * pi / 12) * sin(-pi / 3) + cos(13 * pi / 12) * cos(-pi / 3) = cos(-pi/3)*cos(13*pi/12) - sin(-pi/3)*sin(13*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(13*pi/12) * sin(-pi/3) + cos(13*pi/12) * cos(-pi/3),
{
have : cos(3*pi/4) = cos((13*pi/12) + (-pi/3)),
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


lemma Trigo_number_generalization_step1_149 : -cos(1591*pi/2)=- sin(-pi/4) ** 2 + cos(-pi/4) ** 2:=
begin
have : cos(-pi/2) = -cos(1591*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (397),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_150 : -cos(-pi/4)*cos(5594*pi/3)=- sin(-5*pi/12) / 2 + sin(-pi/12) / 2:=
begin
have : -cos(5594 * pi / 3) * cos(-pi / 4) = -cos(-pi/4)*cos(5594*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(5594*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (932),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(-pi/4) = - sin(-5*pi/12) / 2 + sin(-pi/12) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/4) + (pi/6)) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/4) - (pi/6)) = sin(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_151 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) : (1 - cos(2*pi/3))/sin(2*pi/3)=sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_152 : sin(-2*pi)*sin(-13*pi/8) + cos(-2*pi)*cos(-13*pi/8)=4 * cos(pi/8) ** 3 - 3 * cos(pi/8):=
begin
have : sin((-13) * pi / 8) * sin((-2) * pi) + cos((-13) * pi / 8) * cos((-2) * pi) = sin(-2*pi)*sin(-13*pi/8) + cos(-2*pi)*cos(-13*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = sin(-13*pi/8) * sin(-2*pi) + cos(-13*pi/8) * cos(-2*pi),
{
have : cos(3*pi/8) = cos((-13*pi/8) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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
rw this,
end


lemma Trigo_number_generalization_step1_153 : -tan(2177*pi/8)=- tan(4825*pi/8):=
begin
have : tan(-pi/8) = -tan(2177*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (272),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - tan(4825*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (603),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_154 (h0 : tan(373*pi/6)≠ 0) : -1/tan(373*pi/6)=- sqrt( 3 ):=
begin
have : (-1) / tan(373 * pi / 6) = -1/tan(373*pi/6),
{
field_simp at *,
},
have : tan(2*pi/3) = -1 / tan(373*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi/3) (61),
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


lemma Trigo_number_generalization_step1_155 : -tan(255*pi)=0:=
begin
have : tan(pi) = -tan(255*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (256),
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


lemma Trigo_number_generalization_step1_156 : sin(-pi/3)=2*(-3*cos(-pi/18) + 4*cos(-pi/18)**3)*sin(-pi/6):=
begin
have : 2 * sin(-pi / 6) * (4 * cos(-pi / 18) ** 3 - 3 * cos(-pi / 18)) = 2*(-3*cos(-pi/18) + 4*cos(-pi/18)**3)*sin(-pi/6),
{
field_simp at *,
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


lemma Trigo_number_generalization_step1_157 : sin(-pi/7) + sin(pi)=2*sin(3*pi/7)*cos(6136*pi/7):=
begin
have : cos(-4*pi/7) = cos(6136*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-4*pi/7) (438),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) + sin(pi) = 2 * sin(3*pi/7) * cos(-4*pi/7),
{
rw sin_add_sin,
have : sin(((-pi/7) + (pi))/2) = sin(3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/7) - (pi))/2) = cos(-4*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_158 : sin(5899*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = sin(5899*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (737),
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


lemma Trigo_number_generalization_step1_159 : 2*sin(pi/18)*cos(pi/18)=sin(14383*pi/9):=
begin
have : sin(pi/9) = 2 * sin(pi/18) * cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(14383*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/9) (799),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_160 : -tan(759*pi)=tan(707*pi):=
begin
have : tan(pi) = -tan(759*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (760),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = tan(707*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (706),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_161 : -cos(135*pi/2)=sin(1706*pi):=
begin
have : sin(-pi) = -cos(135*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(1706*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi) (852),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_162 : sin(-pi/8) + sin(pi/4)=2*(1 - 2*sin(-3*pi/32)**2)*sin(pi/16):=
begin
have : 2 * sin(pi / 16) * (1 - 2 * sin((-3) * pi / 32) ** 2) = 2*(1 - 2*sin(-3*pi/32)**2)*sin(pi/16),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-3*pi/16) = 1 - 2 * sin(-3*pi/32) ** 2,
{
have : cos(-3*pi/16) = cos(2*(-3*pi/32)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) + sin(pi/4) = 2 * sin(pi/16) * cos(-3*pi/16),
{
rw sin_add_sin,
have : sin(((-pi/8) + (pi/4))/2) = sin(pi/16),
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
},
rw this,
end


lemma Trigo_number_generalization_step1_163 : sin(3015*pi/8)=- sin(9497*pi/8):=
begin
have : sin(pi/8) = sin(3015*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/8) (188),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = - sin(9497*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/8) (593),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_164 (h0 : -cos(2877*pi/2)≠ 0) (h1 : cos(2877*pi/2)≠ 0) : tan(-pi/2)=-sin(-pi/2)/cos(2877*pi/2):=
begin
have : sin(-pi / 2) / -cos(2877 * pi / 2) = -sin(-pi/2)/cos(2877*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -cos(2877*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (719),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/2) = sin(-pi/2) / cos(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_165 : cos(3817*pi/2)=0:=
begin
have : cos(pi/2) = cos(3817*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (954),
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


lemma Trigo_number_generalization_step1_166 : sin(-2*pi) + sin(pi/7)=2*(-3*cos(-5*pi/14) + 4*cos(-5*pi/14)**3)*sin(-13*pi/14):=
begin
have : 2 * sin((-13) * pi / 14) * (4 * cos((-5) * pi / 14) ** 3 - 3 * cos((-5) * pi / 14)) = 2*(-3*cos(-5*pi/14) + 4*cos(-5*pi/14)**3)*sin(-13*pi/14),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-15*pi/14) = 4 * cos(-5*pi/14) ** 3 - 3 * cos(-5*pi/14),
{
have : cos(-15*pi/14) = cos(3*(-5*pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) + sin(pi/7) = 2 * sin(-13*pi/14) * cos(-15*pi/14),
{
rw sin_add_sin,
have : sin(((-2*pi) + (pi/7))/2) = sin(-13*pi/14),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi/7))/2) = cos(-15*pi/14),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_167 (h0 : sin(7*pi/12)≠ 0) (h1 : (2*sin(7*pi/12))≠ 0) : sin(7*pi/6)/(2*sin(7*pi/12))=- sin(pi/3) * sin(pi/4) + cos(pi/3) * cos(pi/4):=
begin
have : cos(7*pi/12) = sin(7*pi/6) / ( 2 * sin(7*pi/12) ),
{
have : sin(7*pi/6) = sin(2*(7*pi/12)),
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
have : cos(7*pi/12) = - sin(pi/3) * sin(pi/4) + cos(pi/3) * cos(pi/4),
{
have : cos(7*pi/12) = cos((pi/3) + (pi/4)),
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


lemma Trigo_number_generalization_step1_168 : cos(pi/6)=-sin(pi)*cos(5912*pi/3) - sin(5912*pi/3)*cos(pi):=
begin
have : -(sin(5912 * pi / 3) * cos(pi) + sin(pi) * cos(5912 * pi / 3)) = -sin(pi)*cos(5912*pi/3) - sin(5912*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(5915*pi/3) = sin(5912*pi/3) * cos(pi) + sin(pi) * cos(5912*pi/3),
{
have : sin(5915*pi/3) = sin((5912*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = - sin(5915*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (985),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_169 : -sin(pi/9)*sin(5*pi/36) + cos(pi/9)*cos(5*pi/36)=sqrt( 2 ) / 2:=
begin
have : -sin(5 * pi / 36) * sin(pi / 9) + cos(5 * pi / 36) * cos(pi / 9) = -sin(pi/9)*sin(5*pi/36) + cos(pi/9)*cos(5*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(5*pi/36) * sin(pi/9) + cos(5*pi/36) * cos(pi/9),
{
have : cos(pi/4) = cos((5*pi/36) + (pi/9)),
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


lemma Trigo_number_generalization_step1_170 : -sin(pi/7) - sin(3347*pi/3)=2 * sin(2*pi/21) * cos(5*pi/21):=
begin
have : -sin(3347 * pi / 3) - sin(pi / 7) = -sin(pi/7) - sin(3347*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(3347*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (558),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) - sin(pi/7) = 2 * sin(2*pi/21) * cos(5*pi/21),
{
rw sin_sub_sin,
have : cos(((pi/3) + (pi/7))/2) = cos(5*pi/21),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (pi/7))/2) = sin(2*pi/21),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_171 : -1 + 2*cos(pi/4)**2=0:=
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
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step1_172 : cos(-2*pi)=cos(-1588*pi):=
begin
have : - -cos((-1588) * pi) = cos(-1588*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(3439*pi/2) = -cos(-1588*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3439*pi/2) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = - sin(3439*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (860),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_173 (h0 : cos(-pi/7)≠ 0) : cos(355*pi/14)/cos(-pi/7)=tan(-pi/7):=
begin
have : sin(-pi/7) = cos(355*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (12),
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


lemma Trigo_number_generalization_step1_174 : sin(-2*pi) * sin(pi/4)=-cos(-7*pi/4)/2 + sin(1169*pi/4)/2:=
begin
have : sin(1169 * pi / 4) / 2 - cos((-7) * pi / 4) / 2 = -cos(-7*pi/4)/2 + sin(1169*pi/4)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-9*pi/4) = sin(1169*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-9*pi/4) (147),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * sin(pi/4) = cos(-9*pi/4) / 2 - cos(-7*pi/4) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_number_generalization_step1_175 : -sin(874*pi/7)=sin(8119*pi/7):=
begin
have : sin(-pi/7) = -sin(874*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/7) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = sin(8119*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/7) (580),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_176 : -sin(-pi/3)*cos(5*pi/12) + sin(5*pi/12)*cos(-pi/3)=sqrt( 2 ) / 2:=
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


lemma Trigo_number_generalization_step1_177 : sin(5541*pi/8)**2=cos(pi/4) / 2 + 1 / 2:=
begin
have : cos(pi/8) = sin(5541*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/8) (346),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step1_178 : -cos(4693*pi/4)=cos(5889*pi/4):=
begin
have : cos(pi/4) = -cos(4693*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (586),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = cos(5889*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (736),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_179 (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : (1 - cos(2*pi))/sin(2*pi)=0:=
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
have : tan(pi) = 0,
{
rw tan_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_180 (h0 : cos(-2*pi)≠ 0) (h1 : (2*(-sin((-7)*pi/4)*sin(-pi/4)+cos((-7)*pi/4)*cos(-pi/4)))≠ 0) (h2 : (2*(cos(-7*pi/4)*cos(-pi/4)-sin(-7*pi/4)*sin(-pi/4)))≠ 0) : sin(-2*pi)=sin(-4*pi)/(2*(cos(-7*pi/4)*cos(-pi/4) - sin(-7*pi/4)*sin(-pi/4))):=
begin
have : sin((-4) * pi) / (2 * (-sin((-7) * pi / 4) * sin(-pi / 4) + cos((-7) * pi / 4) * cos(-pi / 4))) = sin(-4*pi)/(2*(cos(-7*pi/4)*cos(-pi/4) - sin(-7*pi/4)*sin(-pi/4))),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -sin(-7*pi/4) * sin(-pi/4) + cos(-7*pi/4) * cos(-pi/4),
{
have : cos(-2*pi) = cos((-7*pi/4) + (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_number_generalization_step1_181 (h0 : cos(pi/9)≠ 0) : sin(8000*pi/9)/cos(pi/9)=tan(pi/9):=
begin
have : sin(pi/9) = sin(8000*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (444),
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


lemma Trigo_number_generalization_step1_182 : -cos(417*pi)=1:=
begin
have : sin(pi/2) = -cos(417*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (208),
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


lemma Trigo_number_generalization_step1_183 : -sin(1901*pi/2)=- cos(1282*pi):=
begin
have : cos(-pi) = -sin(1901*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (475),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(1282*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (640),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_184 : sin(-pi)**2 + (-3*cos(-pi/3) + 4*cos(-pi/3)**3)**2=1:=
begin
have : sin(-pi) ** 2 + (4 * cos(-pi / 3) ** 3 - 3 * cos(-pi / 3)) ** 2 = sin(-pi)**2 + (-3*cos(-pi/3) + 4*cos(-pi/3)**3)**2,
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
have : sin(-pi) ** 2 + cos(-pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_185 : cos(-2*pi) - cos(2*pi)=-4*sin(0)*sin(-pi)*cos(-pi):=
begin
have : (-2) * (2 * sin(-pi) * cos(-pi)) * sin(0) = -4*sin(0)*sin(-pi)*cos(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
have : cos(-2*pi) - cos(2*pi) = - 2 * sin(-2*pi) * sin(0),
{
rw cos_sub_cos,
have : sin(((-2*pi) + (2*pi))/2) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-2*pi) - (2*pi))/2) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_186 : (1 - 2*sin(pi/10)**2)**2=1 - sin(pi/5) ** 2:=
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
have : cos(pi/5) ** 2 = 1 - sin(pi/5) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_187 : -1 + 2*cos(pi/12)**2=sqrt( 3 ) / 2:=
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_188 : -4*sin(pi/9)**3 + 3*sin(pi/9)=sqrt( 3 ) / 2:=
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
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_189 : sin(977*pi/4)*cos(pi/7)=cos(11*pi/28) / 2 + cos(-3*pi/28) / 2:=
begin
have : cos(pi / 7) * sin(977 * pi / 4) = sin(977*pi/4)*cos(pi/7),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(977*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/4) (122),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) * cos(-pi/4) = cos(11*pi/28) / 2 + cos(-3*pi/28) / 2,
{
rw cos_mul_cos,
have : cos((pi/7) + (-pi/4)) = cos(-3*pi/28),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/7) - (-pi/4)) = cos(11*pi/28),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_190 : -tan(1829*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = -tan(1829*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (305),
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


lemma Trigo_number_generalization_step1_191 : -cos(227*pi)=1:=
begin
have : sin(pi/2) = -cos(227*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (113),
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


lemma Trigo_number_generalization_step1_192 : 2*sin(pi/14)*cos(pi/14)=- cos(3985*pi/14):=
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
have : sin(pi/7) = - cos(3985*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/7) (142),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_193 : -sin(2607*pi/2)=sin(1317*pi/2):=
begin
have : cos(2*pi) = -sin(2607*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (652),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(1317*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (328),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_194 : sin(25933*pi/18)=2 * cos(pi/9) ** 2 - 1:=
begin
have : cos(2*pi/9) = sin(25933*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/9) (720),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = 2 * cos(pi/9) ** 2 - 1,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_195 : -sin(9067*pi/8)=cos(1009*pi/8):=
begin
have : cos(-pi/8) = -sin(9067*pi/8),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (566),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = cos(1009*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/8) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_196 (h0 : tan(1275*pi/2)≠ 0) : 1/tan(1275*pi/2)=- tan(753*pi):=
begin
have : tan(-pi) = 1 / tan(1275*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (636),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - tan(753*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (752),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_197 : -2*cos(-pi/2)**2 + cos(pi/7) + 1=- 2 * sin(4*pi/7) * sin(-3*pi/7):=
begin
have : cos(pi / 7) - (2 * cos(-pi / 2) ** 2 - 1) = -2*cos(-pi/2)**2 + cos(pi/7) + 1,
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
have : cos(pi/7) - cos(-pi) = - 2 * sin(4*pi/7) * sin(-3*pi/7),
{
rw cos_sub_cos,
have : sin(((pi/7) + (-pi))/2) = sin(-3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/7) - (-pi))/2) = sin(4*pi/7),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_198 (h0 : sin(pi/12)≠ 0) (h1 : (2*sin(pi/12))≠ 0) : sin(pi/6)/(2*sin(pi/12))=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
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


lemma Trigo_number_generalization_step1_199 : -2*sin(-4*pi/15)*cos(-pi/15)=2 * sin(4*pi/15) * cos(-pi/15):=
begin
have : (-1) * (2 * sin((-4) * pi / 15) * cos(-pi / 15)) = -2*sin(-4*pi/15)*cos(-pi/15),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) - sin(pi/5) = 2 * sin(-4*pi/15) * cos(-pi/15),
{
rw sin_sub_sin,
have : cos(((-pi/3) + (pi/5))/2) = cos(-pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (pi/5))/2) = sin(-4*pi/15),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -1*(sin(-pi/3) - sin(pi/5)) = sin(pi/5)-sin(-pi/3),
{
ring,
},
conv {to_lhs, rw this,},
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


lemma Trigo_number_generalization_step1_200 : sin(-2*pi/15)*sin(pi/5) + cos(-2*pi/15)*cos(pi/5)=cos(1045*pi/3):=
begin
have : sin((-2) * pi / 15) * sin(pi / 5) + cos((-2) * pi / 15) * cos(pi / 5) = sin(-2*pi/15)*sin(pi/5) + cos(-2*pi/15)*cos(pi/5),
{
field_simp at *,
},
have : cos(-pi/3) = sin(-2*pi/15) * sin(pi/5) + cos(-2*pi/15) * cos(pi/5),
{
have : cos(-pi/3) = cos((-2*pi/15) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(1045*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (174),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_201 : -cos(423*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -cos(423*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3*pi/4) (52),
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


lemma Trigo_number_generalization_step1_202 : -sin(7814*pi/9)=2 * sin(-pi/9) * cos(-pi/9):=
begin
have : sin(-2*pi/9) = -sin(7814*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi/9) (434),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/9) = 2 * sin(-pi/9) * cos(-pi/9),
{
have : sin(-2*pi/9) = sin(2*(-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_203 : sin(17583*pi/10)=- cos(3626*pi/5):=
begin
have : cos(pi/5) = sin(17583*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (879),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = - cos(3626*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/5) (362),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_204 : -sin(13179*pi/14)=- cos(6714*pi/7):=
begin
have : cos(-pi/7) = -sin(13179*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (470),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = - cos(6714*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/7) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_205 (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : sin(pi)/(2*sin(pi/2))=sin(1769*pi):=
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
have : cos(pi/2) = sin(1769*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (884),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_206 : sin(28267*pi/18)**2=cos(-2*pi/9) / 2 + 1 / 2:=
begin
have : cos(-pi/9) = sin(28267*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (785),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) ** 2 = cos(-2*pi/9) / 2 + 1 / 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
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


lemma Trigo_number_generalization_step1_207 : sin(-pi/2) / cos(-pi/2)=tan(1649*pi/2):=
begin
have : tan(-pi/2) = tan(1649*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (825),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) / cos(-pi/2) = tan(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_208 : sin(9*pi)=cos(2709*pi/2):=
begin
have : cos(pi/2) = sin(9*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(2709*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (677),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_209 : sin(pi/6) * sin(pi/3)=-cos(pi/2)/2 + cos(383*pi/6)/2:=
begin
have : cos(383 * pi / 6) / 2 - cos(pi / 2) / 2 = -cos(pi/2)/2 + cos(383*pi/6)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = cos(383*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) * sin(pi/3) = cos(-pi/6) / 2 - cos(pi/2) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_number_generalization_step1_210 : -cos(171*pi)=1 - 2 * sin(2*pi) ** 2:=
begin
have : cos(4*pi) = -cos(171*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (4*pi) (87),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step1_211 : sin(-4*pi/45)*cos(-pi/5) - sin(-pi/5)*cos(-4*pi/45)=- cos(27997*pi/18):=
begin
have : sin((-4) * pi / 45) * cos(-pi / 5) - sin(-pi / 5) * cos((-4) * pi / 45) = sin(-4*pi/45)*cos(-pi/5) - sin(-pi/5)*cos(-4*pi/45),
{
field_simp at *,
},
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
have : sin(pi/9) = - cos(27997*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (777),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_212 : sin(497*pi/6)=1 / 2:=
begin
have : sin(pi/6) = sin(497*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (41),
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


lemma Trigo_number_generalization_step1_213 : 1 - 2*sin(pi/2)**2=- 1:=
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
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_214 : -sin(-pi/16)**2 + cos(-pi/16)**2=cos(3807*pi/8):=
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
have : cos(-pi/8) = cos(3807*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/8) (238),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_215 : -cos(5348*pi/3)=1 / 2:=
begin
have : sin(pi/6) = -cos(5348*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (891),
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


lemma Trigo_number_generalization_step1_216 : -3*cos(pi/18) + 4*cos(pi/18)**3=sqrt( 3 ) / 2:=
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_217 : sin(-3*pi/2)=-sin(5*pi/2)/2 - sin(3*pi/2)/2 + sin(pi/2)*cos(2*pi):=
begin
have : sin(pi / 2) * cos(2 * pi) - (sin(3 * pi / 2) / 2 + sin(5 * pi / 2) / 2) = -sin(5*pi/2)/2 - sin(3*pi/2)/2 + sin(pi/2)*cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * cos(pi/2) = sin(3*pi/2) / 2 + sin(5*pi/2) / 2,
{
rw sin_mul_cos,
have : sin((2*pi) + (pi/2)) = sin(5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (pi/2)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (sin(2*pi) * cos(pi/2)) = sin(2*pi)*cos(pi/2),
{
ring,
},
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


lemma Trigo_number_generalization_step1_218 : -4*sin(pi/6)**3 + 3*sin(pi/6)=1:=
begin
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


lemma Trigo_number_generalization_step1_219 (h0 : cos(-pi)≠ 0) (h1 : (2*cos(-pi))≠ 0) : cos(5*pi/6)=cos(-pi)*cos(-pi/6) + sin(-2*pi)*sin(-pi/6)/(2*cos(-pi)):=
begin
have : sin(-pi / 6) * (sin((-2) * pi) / (2 * cos(-pi))) + cos(-pi / 6) * cos(-pi) = cos(-pi)*cos(-pi/6) + sin(-2*pi)*sin(-pi/6)/(2*cos(-pi)),
{
field_simp at *,
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
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_220 : -sin(55741*pi/45)=sin(-pi/5) * cos(pi/9) - sin(pi/9) * cos(-pi/5):=
begin
have : sin(-14*pi/45) = -sin(55741*pi/45),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-14*pi/45) (619),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-14*pi/45) = sin(-pi/5) * cos(pi/9) - sin(pi/9) * cos(-pi/5),
{
have : sin(-14*pi/45) = sin((-pi/5) - (pi/9)),
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


lemma Trigo_number_generalization_step1_221 (h0 : cos((pi/4)/2)≠ 0) (h1 : sin(pi/4)≠ 0) : (1 - cos(pi/4))/sin(pi/4)=tan(4329*pi/8):=
begin
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
have : tan(pi/8) = tan(4329*pi/8),
{
rw tan_eq_tan_add_int_mul_pi (pi/8) (541),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_222 : sin(2*pi) ** 2=1 - cos(1685*pi)**2:=
begin
have : 1 - (-cos(1685 * pi)) ** 2 = 1 - cos(1685*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -cos(1685*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (841),
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


lemma Trigo_number_generalization_step1_223 : -sin(13*pi/42)/2 + sin(-pi/42)/2=sin(-13*pi/42) / 2 + sin(-pi/42) / 2:=
begin
have : sin(-pi/6) * cos(pi/7) = -sin(13*pi/42) / 2 + sin(-pi/42) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/7) + (-pi/6)) = sin(-pi/42),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/7) - (-pi/6)) = sin(13*pi/42),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi/6) * cos(pi/7)) = sin(-pi/6)*cos(pi/7),
{
ring,
},
have : sin(-pi/6) * cos(pi/7) = sin(-13*pi/42) / 2 + sin(-pi/42) / 2,
{
rw sin_mul_cos,
have : sin((-pi/6) + (pi/7)) = sin(-pi/42),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (pi/7)) = sin(-13*pi/42),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_224 : cos(1674*pi)=- sin(pi) ** 2 + cos(pi) ** 2:=
begin
have : cos(2*pi) = cos(1674*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (838),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_number_generalization_step1_225 : sin(1868*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = sin(1868*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (311),
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


lemma Trigo_number_generalization_step1_226 : -cos(7888*pi/7)=cos(1455*pi/7):=
begin
have : cos(pi/7) = -cos(7888*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/7) (563),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = cos(1455*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/7) (104),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_227 : -sin(-pi/14)**2 + cos(-pi/14)**2=cos(967*pi/7):=
begin
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
have : cos(-pi/7) = cos(967*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/7) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_228 : cos(1832*pi)**2=1 / 2 - cos(pi) / 2:=
begin
have : sin(pi/2) = cos(1832*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (916),
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


lemma Trigo_number_generalization_step1_229 : -sin(1923*pi/2)=- cos(1019*pi):=
begin
have : cos(-2*pi) = -sin(1923*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - cos(1019*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (508),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_230 : sin(pi/2)*cos(15185*pi/8)=- sin(-3*pi/8) / 2 + sin(5*pi/8) / 2:=
begin
have : cos(pi/8) = cos(15185*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/8) (949),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(pi/8) = - sin(-3*pi/8) / 2 + sin(5*pi/8) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/8) + (pi/2)) = sin(5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (pi/2)) = sin(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_231 : cos(-2*pi/9)=1 - 2*sin(10387*pi/9)**2:=
begin
have : 1 - 2 * (-sin(10387 * pi / 9)) ** 2 = 1 - 2*sin(10387*pi/9)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) = -sin(10387*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/9) (577),
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


lemma Trigo_number_generalization_step1_232 (h0 : cos(4*pi/21)≠ 0) (h1 : cos(-pi/7)≠ 0) (h2 : (tan(-pi/7)*tan(4*pi/21)+1)≠ 0) (h3 : (1+tan(4*pi/21)*tan(-pi/7))≠ 0) : (-tan(-pi/7) + tan(4*pi/21))/(tan(-pi/7)*tan(4*pi/21) + 1)=sqrt( 3 ):=
begin
have : (tan(4 * pi / 21) - tan(-pi / 7)) / (1 + tan(4 * pi / 21) * tan(-pi / 7)) = (-tan(-pi/7) + tan(4*pi/21))/(tan(-pi/7)*tan(4*pi/21) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = ( tan(4*pi/21) - tan(-pi/7) ) / ( 1 + tan(4*pi/21) * tan(-pi/7) ),
{
have : tan(pi/3) = tan((4*pi/21) - (-pi/7)),
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


lemma Trigo_number_generalization_step1_233 : -3*cos(-pi/9) + 4*cos(-pi/9)**3=- sin(-pi/6) ** 2 + cos(-pi/6) ** 2:=
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
have : cos(-pi/3) = - sin(-pi/6) ** 2 + cos(-pi/6) ** 2,
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
rw this,
end


lemma Trigo_number_generalization_step1_234 : -sin(pi/4)**2 + cos(pi/4)**2=0:=
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
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step1_235 : -sin(-pi/7)*cos(5*pi/14) + sin(5*pi/14)*cos(-pi/7)=- cos(905*pi):=
begin
have : sin(5 * pi / 14) * cos(-pi / 7) - sin(-pi / 7) * cos(5 * pi / 14) = -sin(-pi/7)*cos(5*pi/14) + sin(5*pi/14)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(5*pi/14) * cos(-pi/7) - sin(-pi/7) * cos(5*pi/14),
{
have : sin(pi/2) = sin((5*pi/14) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - cos(905*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (452),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_236 : cos(pi/4)=-1 + 2*cos(pi/8)**2:=
begin
have : 1 - 2 * (1 - cos(pi / 8) ** 2) = -1 + 2*cos(pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) ** 2 = 1 - cos(pi/8) ** 2,
{
rw sin_sq,
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


lemma Trigo_number_generalization_step1_237 : (-sin(-pi/9)*cos(8*pi/9) + sin(8*pi/9)*cos(-pi/9))**2=1 / 2 - cos(2*pi) / 2:=
begin
have : (sin(8 * pi / 9) * cos(-pi / 9) - sin(-pi / 9) * cos(8 * pi / 9)) ** 2 = (-sin(-pi/9)*cos(8*pi/9) + sin(8*pi/9)*cos(-pi/9))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(8*pi/9) * cos(-pi/9) - sin(-pi/9) * cos(8*pi/9),
{
have : sin(pi) = sin((8*pi/9) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) ** 2 = 1 / 2 - cos(2*pi) / 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_238 : cos(-pi/2)=1 - 2*(sin(-11*pi/28)*cos(-pi/7) - sin(-pi/7)*cos(-11*pi/28))**2:=
begin
have : 1 - 2 * (sin((-11) * pi / 28) * cos(-pi / 7) - sin(-pi / 7) * cos((-11) * pi / 28)) ** 2 = 1 - 2*(sin(-11*pi/28)*cos(-pi/7) - sin(-pi/7)*cos(-11*pi/28))**2,
{
field_simp at *,
},
have : sin(-pi/4) = sin(-11*pi/28) * cos(-pi/7) - sin(-pi/7) * cos(-11*pi/28),
{
have : sin(-pi/4) = sin((-11*pi/28) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
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


lemma Trigo_number_generalization_step1_239 : -sin(5968*pi/3)=- 4 * sin(pi/9) ** 3 + 3 * sin(pi/9):=
begin
have : sin(pi/3) = -sin(5968*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (994),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - 4 * sin(pi/9) ** 3 + 3 * sin(pi/9),
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
rw this,
end


lemma Trigo_number_generalization_step1_240 : sin(-pi/9) + sin(pi/6)=2*sin(pi/36)*sin(1679*pi/36):=
begin
have : cos(-5*pi/36) = sin(1679*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-5*pi/36) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/9) + sin(pi/6) = 2 * sin(pi/36) * cos(-5*pi/36),
{
rw sin_add_sin,
have : sin(((-pi/9) + (pi/6))/2) = sin(pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (pi/6))/2) = cos(-5*pi/36),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_241 : -2*sin(pi/4)**2 + cos(pi/5) + 1=2 * cos(3*pi/20) * cos(7*pi/20):=
begin
have : 1 - 2 * sin(pi / 4) ** 2 + cos(pi / 5) = -2*sin(pi/4)**2 + cos(pi/5) + 1,
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
have : cos(pi/2) + cos(pi/5) = 2 * cos(3*pi/20) * cos(7*pi/20),
{
rw cos_add_cos,
have : cos(((pi/2) + (pi/5))/2) = cos(7*pi/20),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/2) - (pi/5))/2) = cos(3*pi/20),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_242 : cos(3295*pi/6)=- sin(3704*pi/3):=
begin
have : sin(-pi/3) = cos(3295*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (274),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(3704*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (617),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_243 : -sin(2683*pi/2)=- sin(pi) ** 2 + cos(pi) ** 2:=
begin
have : cos(2*pi) = -sin(2683*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (671),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_number_generalization_step1_244 : -sin(13633*pi/10)=cos(3021*pi/5):=
begin
have : cos(-pi/5) = -sin(13633*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (681),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = cos(3021*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/5) (302),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_245 (h0 : cos((-pi/4)/2)≠ 0) (h1 : sin(-pi/4)≠ 0) : (1 - cos(-pi/4))/sin(-pi/4)=1 / tan(3357*pi/8):=
begin
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
have : tan(-pi/8) = 1 / tan(3357*pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/8) (419),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_246 : -cos(5860*pi/3) - sin(-pi/4)=2 * sin(5*pi/24) * cos(-pi/24):=
begin
have : sin(pi/6) = -cos(5860*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (976),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) - sin(-pi/4) = 2 * sin(5*pi/24) * cos(-pi/24),
{
rw sin_sub_sin,
have : cos(((pi/6) + (-pi/4))/2) = cos(-pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/6) - (-pi/4))/2) = sin(5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_247 (h0 : tan(6739*pi/12)≠ 0) : -1/tan(6739*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / tan(6739 * pi / 12) = -1/tan(6739*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(6739*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (561),
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


lemma Trigo_number_generalization_step1_248 : -cos(3009*pi/2)=0:=
begin
have : cos(pi/2) = -cos(3009*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (752),
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


lemma Trigo_number_generalization_step1_249 : sin(-2*pi)=-cos(3101*pi/2):=
begin
have : cos(1567*pi/2) = -cos(3101*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (1567*pi/2) (383),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = cos(1567*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (392),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_250 : sin(3329*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(3329*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (416),
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


lemma Trigo_number_generalization_step1_251 (h0 : cos(pi/4)≠ 0) : sin(pi/4)/cos(pi/4)=1:=
begin
have : tan(pi/4) = sin(pi/4) / cos(pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_252 : sin(1603*pi/4)=2 * cos(-pi/8) ** 2 - 1:=
begin
have : cos(-pi/4) = sin(1603*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (200),
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


lemma Trigo_number_generalization_step1_253 (h0 : tan(1273*pi/4)≠ 0) : 1/tan(1273*pi/4)=1:=
begin
have : tan(pi/4) = 1 / tan(1273*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (318),
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


lemma Trigo_number_generalization_step1_254 : -sin(5146*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -sin(5146*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (857),
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


lemma Trigo_number_generalization_step1_255 : cos(-pi/9)*cos(775*pi)=cos(-8*pi/9) / 2 + cos(-10*pi/9) / 2:=
begin
have : cos(775 * pi) * cos(-pi / 9) = cos(-pi/9)*cos(775*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(775*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (387),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(-pi/9) = cos(-8*pi/9) / 2 + cos(-10*pi/9) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (-pi/9)) = cos(-10*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (-pi/9)) = cos(-8*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_256 : cos(2843*pi/2)**2 + cos(pi)**2=1:=
begin
have : (-cos(2843 * pi / 2)) ** 2 + cos(pi) ** 2 = cos(2843*pi/2)**2 + cos(pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(2843*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (710),
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


lemma Trigo_number_generalization_step1_257 : -tan(1825*pi/3)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = -tan(1825*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (609),
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


lemma Trigo_number_generalization_step1_258 : cos(-12*pi/35)=-cos(2*pi/35)/2 + cos(-12*pi/35)/2 + cos(-pi/5)*cos(-pi/7):=
begin
have : -(cos(2 * pi / 35) / 2 - cos((-12) * pi / 35) / 2) + cos(-pi / 5) * cos(-pi / 7) = -cos(2*pi/35)/2 + cos(-12*pi/35)/2 + cos(-pi/5)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/7) * sin(-pi/5) = cos(2*pi/35) / 2 - cos(-12*pi/35) / 2,
{
rw sin_mul_sin,
have : cos((-pi/7) + (-pi/5)) = cos(-12*pi/35),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/7) - (-pi/5)) = cos(2*pi/35),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -(sin(-pi/7) * sin(-pi/5)) = -sin(-pi/5)*sin(-pi/7),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-12*pi/35) = - sin(-pi/5) * sin(-pi/7) + cos(-pi/5) * cos(-pi/7),
{
have : cos(-12*pi/35) = cos((-pi/5) + (-pi/7)),
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


lemma Trigo_number_generalization_step1_259 : sin(3*pi/2)*cos(pi/2) - sin(pi/2)*cos(3*pi/2)=0:=
begin
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_260 : sin(13697*pi/9)=cos(18637*pi/18):=
begin
have : sin(-pi/9) = sin(13697*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/9) (761),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = cos(18637*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (517),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_261 : tan(865*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = tan(865*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (144),
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


lemma Trigo_number_generalization_step1_262 : -sin(pi/5)*cos(957*pi/4)=sin(9*pi/20) / 2 + sin(-pi/20) / 2:=
begin
have : sin(pi / 5) * -cos(957 * pi / 4) = -sin(pi/5)*cos(957*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -cos(957*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (119),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) * cos(-pi/4) = sin(9*pi/20) / 2 + sin(-pi/20) / 2,
{
rw sin_mul_cos,
have : sin((pi/5) + (-pi/4)) = sin(-pi/20),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (-pi/4)) = sin(9*pi/20),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_263 (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : sin(pi)/(2*cos(pi/2))=1:=
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step1_264 : cos(pi/2)=-cos(-2019*pi/2):=
begin
have : -cos((-2019) * pi / 2) = -cos(-2019*pi/2),
{
field_simp at *,
},
have : sin(1926*pi) = cos(-2019*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (1926*pi) (458),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(1926*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (962),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_265 (h0 : cos(11*pi/5)≠ 0) (h1 : cos(pi/5)≠ 0) (h2 : (tan(pi/5)*tan(11*pi/5)+1)≠ 0) (h3 : (1+tan(11*pi/5)*tan(pi/5))≠ 0) : (-tan(pi/5) + tan(11*pi/5))/(tan(pi/5)*tan(11*pi/5) + 1)=- tan(188*pi):=
begin
have : (tan(11 * pi / 5) - tan(pi / 5)) / (1 + tan(11 * pi / 5) * tan(pi / 5)) = (-tan(pi/5) + tan(11*pi/5))/(tan(pi/5)*tan(11*pi/5) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = ( tan(11*pi/5) - tan(pi/5) ) / ( 1 + tan(11*pi/5) * tan(pi/5) ),
{
have : tan(2*pi) = tan((11*pi/5) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - tan(188*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (190),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_266 : cos(1630*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(1630*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (272),
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


lemma Trigo_number_generalization_step1_267 : sin(5*pi/36)=sin(-pi/9)*cos(-pi/4) + sin(-pi/4)*cos(5968*pi/9):=
begin
have : sin(-pi / 9) * cos(-pi / 4) - sin(-pi / 4) * -cos(5968 * pi / 9) = sin(-pi/9)*cos(-pi/4) + sin(-pi/4)*cos(5968*pi/9),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = -cos(5968*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/9) (331),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/36) = sin(-pi/9) * cos(-pi/4) - sin(-pi/4) * cos(-pi/9),
{
have : sin(5*pi/36) = sin((-pi/9) - (-pi/4)),
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


lemma Trigo_number_generalization_step1_268 : 2*sin(pi)*cos(pi)=- sin(1467*pi):=
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
have : sin(2*pi) = - sin(1467*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (732),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_269 : 4*sin(pi/10)**2*cos(pi/10)**2=1 - cos(pi/5) ** 2:=
begin
have : (2 * sin(pi / 10) * cos(pi / 10)) ** 2 = 4*sin(pi/10)**2*cos(pi/10)**2,
{
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
have : sin(pi/5) ** 2 = 1 - cos(pi/5) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_270 : -cos(-2*pi) - sin(-pi/4)**2 + cos(-pi/4)**2=- 2 * sin(3*pi/4) * sin(-5*pi/4):=
begin
have : -sin(-pi / 4) ** 2 + cos(-pi / 4) ** 2 - cos((-2) * pi) = -cos(-2*pi) - sin(-pi/4)**2 + cos(-pi/4)**2,
{
field_simp at *,
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
have : cos(-pi/2) - cos(-2*pi) = - 2 * sin(3*pi/4) * sin(-5*pi/4),
{
rw cos_sub_cos,
have : sin(((-pi/2) + (-2*pi))/2) = sin(-5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (-2*pi))/2) = sin(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_271 : sin(4501*pi/6)=2 * cos(-pi/6) ** 2 - 1:=
begin
have : cos(-pi/3) = sin(4501*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (375),
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


lemma Trigo_number_generalization_step1_272 : sin(7617*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(7617*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (952),
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


lemma Trigo_number_generalization_step1_273 : -sin(4409*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -sin(4409*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (734),
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


lemma Trigo_number_generalization_step1_274 (h0 : tan(5479*pi/18)≠ 0) : -1/tan(5479*pi/18)=tan(2717*pi/9):=
begin
have : (-1) / tan(5479 * pi / 18) = -1/tan(5479*pi/18),
{
field_simp at *,
},
have : tan(-pi/9) = -1 / tan(5479*pi/18),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/9) (304),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/9) = tan(2717*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (-pi/9) (302),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_275 : 2*sin(pi/4)*cos(pi/4)=1:=
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step1_276 : (-3*cos(-pi/21) + 4*cos(-pi/21)**3)**2=cos(-2*pi/7) / 2 + 1 / 2:=
begin
have : (4 * cos(-pi / 21) ** 3 - 3 * cos(-pi / 21)) ** 2 = (-3*cos(-pi/21) + 4*cos(-pi/21)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = 4 * cos(-pi/21) ** 3 - 3 * cos(-pi/21),
{
have : cos(-pi/7) = cos(3*(-pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
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


lemma Trigo_number_generalization_step1_277 : sin(12263*pi/10)=cos(4219*pi/5):=
begin
have : cos(-pi/5) = sin(12263*pi/10),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/5) (613),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = cos(4219*pi/5),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/5) (422),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_278 : -sin(4021*pi/18)=- cos(3932*pi/9):=
begin
have : cos(-pi/9) = -sin(4021*pi/18),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (111),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = - cos(3932*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/9) (218),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_279 (h0 : tan(4483*pi/12)≠ 0) : -1/tan(4483*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / tan(4483 * pi / 12) = -1/tan(4483*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(4483*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (373),
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


lemma Trigo_number_generalization_step1_280 : sin(pi/2)*sin(7*pi/6) + cos(pi/2)*cos(7*pi/6)=- 1 / 2:=
begin
have : sin(7 * pi / 6) * sin(pi / 2) + cos(7 * pi / 6) * cos(pi / 2) = sin(pi/2)*sin(7*pi/6) + cos(pi/2)*cos(7*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(7*pi/6) * sin(pi/2) + cos(7*pi/6) * cos(pi/2),
{
have : cos(2*pi/3) = cos((7*pi/6) - (pi/2)),
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


lemma Trigo_number_generalization_step1_281 (h0 : cos(3*pi/8)≠ 0) (h1 : (1-tan(3*pi/8)**2)≠ 0) : 2*tan(3*pi/8)/(1 - tan(3*pi/8)**2)=- 1:=
begin
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


lemma Trigo_number_generalization_step1_282 : sin(-pi/3)*sin(1299*pi/8)=- sin(11*pi/24) / 2 + sin(-5*pi/24) / 2:=
begin
have : cos(pi/8) = sin(1299*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/8) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi/8) = - sin(11*pi/24) / 2 + sin(-5*pi/24) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/8) + (-pi/3)) = sin(-5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (-pi/3)) = sin(11*pi/24),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_283 : cos(19933*pi/18)=- cos(30521*pi/18):=
begin
have : sin(-pi/9) = cos(19933*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (553),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = - cos(30521*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (847),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_284 (h0 : tan(5365*pi/6)≠ 0) : 1/tan(5365*pi/6)=sqrt( 3 ):=
begin
have : tan(pi/3) = 1 / tan(5365*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (894),
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


lemma Trigo_number_generalization_step1_285 : sin(2*pi) * sin(pi/7)=-1/2 - cos(15*pi/7)/2 + cos(13*pi/14)**2:=
begin
have : (2 * cos(13 * pi / 14) ** 2 - 1) / 2 - cos(15 * pi / 7) / 2 = -1/2 - cos(15*pi/7)/2 + cos(13*pi/14)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(13*pi/7) = 2 * cos(13*pi/14) ** 2 - 1,
{
have : cos(13*pi/7) = cos(2*(13*pi/14)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * sin(pi/7) = cos(13*pi/7) / 2 - cos(15*pi/7) / 2,
{
rw sin_mul_sin,
have : cos((2*pi) + (pi/7)) = cos(15*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (pi/7)) = cos(13*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_286 : sin(-4*pi)=-2*sin(-2*pi)*cos(317*pi):=
begin
have : 2 * sin((-2) * pi) * -cos(317 * pi) = -2*sin(-2*pi)*cos(317*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -cos(317*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (157),
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


lemma Trigo_number_generalization_step1_287 : -cos(760*pi/3)=1 / 2:=
begin
have : sin(pi/6) = -cos(760*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (126),
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


lemma Trigo_number_generalization_step1_288 : cos(-pi/2) - sin(3413*pi/3)=2 * cos(pi/3) * cos(-pi/6):=
begin
have : -sin(3413 * pi / 3) + cos(-pi / 2) = cos(-pi/2) - sin(3413*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(3413*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (568),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step1_289 (h0 : cos(5353*pi/6)≠ 0) : tan(pi/6)=sin(pi/6)/cos(5353*pi/6):=
begin
have : cos(pi/6) = cos(5353*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (446),
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


lemma Trigo_number_generalization_step1_290 : cos(2*pi/5)=-sin(6971*pi/5)**2 + cos(pi/5)**2:=
begin
have : sin(pi/5) = sin(6971*pi/5),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/5) (697),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_291 (h0 : sin(3*pi/4)≠ 0) (h1 : (2*sin(3*pi/4))≠ 0) : sin(3*pi/2)/(2*sin(3*pi/4))=- sqrt( 2 ) / 2:=
begin
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
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = - sqrt( 2 ) / 2,
{
rw cos_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_292 : sin(-7*pi/60)*cos(pi/5) + sin(pi/5)*cos(-7*pi/60)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin((-7) * pi / 60) * cos(pi / 5) + sin(pi / 5) * cos((-7) * pi / 60) = sin(-7*pi/60)*cos(pi/5) + sin(pi/5)*cos(-7*pi/60),
{
field_simp at *,
},
have : sin(pi/12) = sin(-7*pi/60) * cos(pi/5) + sin(pi/5) * cos(-7*pi/60),
{
have : sin(pi/12) = sin((-7*pi/60) + (pi/5)),
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


lemma Trigo_number_generalization_step1_293 : sin(5193*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = sin(5193*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (649),
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


lemma Trigo_number_generalization_step1_294 (h0 : cos((pi/6)/2)≠ 0) (h1 : sin(pi/6)≠ 0) : (1 - cos(pi/6))/sin(pi/6)=2 - sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_295 : cos(pi/12)=cos(-pi/3)*cos(-pi/4) - sin(-pi/4)*cos(8603*pi/6):=
begin
have : sin(-pi / 4) * -cos(8603 * pi / 6) + cos(-pi / 4) * cos(-pi / 3) = cos(-pi/3)*cos(-pi/4) - sin(-pi/4)*cos(8603*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = -cos(8603*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (716),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/12) = sin(-pi/4) * sin(-pi/3) + cos(-pi/4) * cos(-pi/3),
{
have : cos(pi/12) = cos((-pi/4) - (-pi/3)),
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


lemma Trigo_number_generalization_step1_296 : -cos(493*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = -cos(493*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (61),
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


lemma Trigo_number_generalization_step1_297 : -1 + 2*cos(pi/2)**2=- 1:=
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
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_298 : sin(7131*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(7131*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (3*pi/4) (891),
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


lemma Trigo_number_generalization_step1_299 : cos(7935*pi/4)=- cos(4291*pi/4):=
begin
have : cos(-pi/4) = cos(7935*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/4) (992),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - cos(4291*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/4) (536),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_300 : cos(2732*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(2732*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (455),
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


lemma Trigo_number_generalization_step1_301 (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : sin(2*pi/3)/(2*cos(pi/3))=sin(5126*pi/3):=
begin
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
have : sin(pi/3) = sin(5126*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (854),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_302 : cos(pi/8) ** 2=1 - cos(14597*pi/8)**2:=
begin
have : 1 - (-cos(14597 * pi / 8)) ** 2 = 1 - cos(14597*pi/8)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) = -cos(14597*pi/8),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/8) (912),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) ** 2 = 1 - sin(pi/8) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_303 (h0 : sin(1697*pi)≠ 0) (h1 : -sin(1697*pi)≠ 0) : -sin(-pi/2)/sin(1697*pi)=tan(-pi/2):=
begin
have : sin(-pi / 2) / -sin(1697 * pi) = -sin(-pi/2)/sin(1697*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(1697*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (848),
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


lemma Trigo_number_generalization_step1_304 : (sin(-pi/9)*sin(pi/72) + cos(-pi/9)*cos(pi/72))**2=cos(pi/4) / 2 + 1 / 2:=
begin
have : (sin(pi / 72) * sin(-pi / 9) + cos(pi / 72) * cos(-pi / 9)) ** 2 = (sin(-pi/9)*sin(pi/72) + cos(-pi/9)*cos(pi/72))**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = sin(pi/72) * sin(-pi/9) + cos(pi/72) * cos(-pi/9),
{
have : cos(pi/8) = cos((pi/72) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_number_generalization_step1_305 : sin(pi) + sin(-pi/8)=2*sin(7*pi/16)*cos(16151*pi/16):=
begin
have : cos(9*pi/16) = cos(16151*pi/16),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (9*pi/16) (505),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) + sin(-pi/8) = 2 * sin(7*pi/16) * cos(9*pi/16),
{
rw sin_add_sin,
have : sin(((pi) + (-pi/8))/2) = sin(7*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (-pi/8))/2) = cos(9*pi/16),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_306 : cos(-pi/3) - cos(3685*pi/4)=2 * cos(-7*pi/24) * cos(-pi/24):=
begin
have : cos(-pi / 3) + -cos(3685 * pi / 4) = cos(-pi/3) - cos(3685*pi/4),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(3685*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (460),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(pi/4) = 2 * cos(-7*pi/24) * cos(-pi/24),
{
rw cos_add_cos,
have : cos(((-pi/3) + (pi/4))/2) = cos(-pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (pi/4))/2) = cos(-7*pi/24),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_307 (h0 : cos(pi)≠ 0) : tan(pi)=cos(3907*pi/2)/cos(pi):=
begin
have : sin(pi) = cos(3907*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (977),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_308 : (-sin(pi)**2 + cos(pi)**2)*cos(-pi/5)=cos(-11*pi/5) / 2 + cos(9*pi/5) / 2:=
begin
have : cos(-pi / 5) * (-sin(pi) ** 2 + cos(pi) ** 2) = (-sin(pi)**2 + cos(pi)**2)*cos(-pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
have : cos(-pi/5) * cos(2*pi) = cos(-11*pi/5) / 2 + cos(9*pi/5) / 2,
{
rw cos_mul_cos,
have : cos((-pi/5) + (2*pi)) = cos(9*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/5) - (2*pi)) = cos(-11*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_309 (h0 : cos(-pi)≠ 0) (h1 : (1-tan(-pi)**2)≠ 0) : 2*tan(-pi)/(1 - tan(-pi)**2)=1 / tan(1213*pi/2):=
begin
have : tan(-2*pi) = 2 * tan(-pi) / ( 1 - tan(-pi) ** 2 ),
{
have : tan(-2*pi) = tan(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = 1 / tan(1213*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-2*pi) (604),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_310 : cos(-pi/6)=cos(6553*pi/6):=
begin
have : - -cos(6553 * pi / 6) = cos(6553*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(335*pi/3) = -cos(6553*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (335*pi/3) (490),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(335*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_311 : cos(2873*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = cos(2873*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (359),
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


lemma Trigo_number_generalization_step1_312 : -1 + 2*cos(pi)**2=- cos(669*pi):=
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
have : cos(2*pi) = - cos(669*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (335),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_313 (h0 : sin(pi/3)≠ 0) (h1 : (2*sin(pi/3))≠ 0) : sin(2*pi/3)/(2*sin(pi/3)) - cos(-pi)=- 2 * sin(2*pi/3) * sin(-pi/3):=
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
have : cos(pi/3) - cos(-pi) = - 2 * sin(2*pi/3) * sin(-pi/3),
{
rw cos_sub_cos,
have : sin(((pi/3) + (-pi))/2) = sin(-pi/3),
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_314 (h0 : cos(pi/8)≠ 0) (h1 : (2*cos(pi/8))≠ 0) : -sin(pi/4)/(2*cos(pi/8)) + sin(pi/9)=2 * sin(-pi/144) * cos(17*pi/144):=
begin
have : sin(pi / 9) - sin(pi / 4) / (2 * cos(pi / 8)) = -sin(pi/4)/(2*cos(pi/8)) + sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = sin(pi/4) / ( 2 * cos(pi/8) ),
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
have : sin(pi/9) - sin(pi/8) = 2 * sin(-pi/144) * cos(17*pi/144),
{
rw sin_sub_sin,
have : cos(((pi/9) + (pi/8))/2) = cos(17*pi/144),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/9) - (pi/8))/2) = sin(-pi/144),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_315 : -cos(2973*pi/5)=- sin(-pi/5) ** 2 + cos(-pi/5) ** 2:=
begin
have : cos(-2*pi/5) = -cos(2973*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/5) (297),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_316 : sin(-pi/9)*cos(4*pi/9) + sin(4*pi/9)*cos(-pi/9)=sqrt( 3 ) / 2:=
begin
have : sin(4 * pi / 9) * cos(-pi / 9) + sin(-pi / 9) * cos(4 * pi / 9) = sin(-pi/9)*cos(4*pi/9) + sin(4*pi/9)*cos(-pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(4*pi/9) * cos(-pi/9) + sin(-pi/9) * cos(4*pi/9),
{
have : sin(pi/3) = sin((4*pi/9) + (-pi/9)),
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


lemma Trigo_number_generalization_step1_317 : 2*sin(pi/12)*cos(pi/12)=1 / 2:=
begin
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
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_318 : sin(-2*pi) / cos(-2*pi)=-tan(700*pi):=
begin
have : tan(-2*pi) = -tan(700*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-2*pi) (698),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) / cos(-2*pi) = tan(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_319 : sin(-3*pi/40)=-sin(-pi/5)*cos(4743*pi/8) + sin(pi/8)*cos(-pi/5):=
begin
have : sin(pi / 8) * cos(-pi / 5) + sin(-pi / 5) * -cos(4743 * pi / 8) = -sin(-pi/5)*cos(4743*pi/8) + sin(pi/8)*cos(-pi/5),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = -cos(4743*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/8) (296),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/40) = sin(pi/8) * cos(-pi/5) + sin(-pi/5) * cos(pi/8),
{
have : sin(-3*pi/40) = sin((pi/8) + (-pi/5)),
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


lemma Trigo_number_generalization_step1_320 (h0 : cos(pi/7)≠ 0) : sin(pi/7)/cos(pi/7)=- 1 / tan(4433*pi/14):=
begin
have : tan(pi/7) = sin(pi/7) / cos(pi/7),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/7) = - 1 / tan(4433*pi/14),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/7) (316),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_321 (h0 : cos(-pi/18)≠ 0) (h1 : (1-tan(-pi/18)**2)≠ 0) : 2*tan(-pi/18)/(1 - tan(-pi/18)**2)=tan(8873*pi/9):=
begin
have : tan(-pi/9) = 2 * tan(-pi/18) / ( 1 - tan(-pi/18) ** 2 ),
{
have : tan(-pi/9) = tan(2*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/9) = tan(8873*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (-pi/9) (986),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_322 : sin(7503*pi/4)=- sin(2257*pi/4):=
begin
have : sin(-pi/4) = sin(7503*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/4) (938),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = - sin(2257*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (282),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_323 : cos(0)=sin(-pi/6)*sin(3415*pi/6) + cos(-pi/6)*cos(pi/6):=
begin
have : -sin(-pi / 6) * -sin(3415 * pi / 6) + cos(-pi / 6) * cos(pi / 6) = sin(-pi/6)*sin(3415*pi/6) + cos(-pi/6)*cos(pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -sin(3415*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (284),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(0) = - sin(-pi/6) * sin(pi/6) + cos(-pi/6) * cos(pi/6),
{
have : cos(0) = cos((-pi/6) + (pi/6)),
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


lemma Trigo_number_generalization_step1_324 (h0 : cos(4*pi/21)≠ 0) (h1 : cos(pi/3)≠ 0) (h2 : (1+tan(4*pi/21)*tan(pi/3))≠ 0) : (-tan(pi/3) + tan(4*pi/21))/(1 + tan(4*pi/21)*tan(pi/3))=- tan(2577*pi/7):=
begin
have : (tan(4 * pi / 21) - tan(pi / 3)) / (1 + tan(4 * pi / 21) * tan(pi / 3)) = (-tan(pi/3) + tan(4*pi/21))/(1 + tan(4*pi/21)*tan(pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/7) = ( tan(4*pi/21) - tan(pi/3) ) / ( 1 + tan(4*pi/21) * tan(pi/3) ),
{
have : tan(-pi/7) = tan((4*pi/21) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/7) = - tan(2577*pi/7),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/7) (368),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_325 : -cos(pi/6) + sin(7*pi/4)*sin(2*pi) + cos(7*pi/4)*cos(2*pi)=- 2 * sin(-5*pi/24) * sin(-pi/24):=
begin
have : sin(7 * pi / 4) * sin(2 * pi) + cos(7 * pi / 4) * cos(2 * pi) - cos(pi / 6) = -cos(pi/6) + sin(7*pi/4)*sin(2*pi) + cos(7*pi/4)*cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = sin(7*pi/4) * sin(2*pi) + cos(7*pi/4) * cos(2*pi),
{
have : cos(-pi/4) = cos((7*pi/4) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) - cos(pi/6) = - 2 * sin(-5*pi/24) * sin(-pi/24),
{
rw cos_sub_cos,
have : sin(((-pi/4) + (pi/6))/2) = sin(-pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/4) - (pi/6))/2) = sin(-5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_326 : sin(-pi/5)*cos(8*pi/15) + sin(8*pi/15)*cos(-pi/5)=sqrt( 3 ) / 2:=
begin
have : sin(8 * pi / 15) * cos(-pi / 5) + sin(-pi / 5) * cos(8 * pi / 15) = sin(-pi/5)*cos(8*pi/15) + sin(8*pi/15)*cos(-pi/5),
{
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_327 : cos(1970*pi)=1:=
begin
have : sin(pi/2) = cos(1970*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (984),
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


lemma Trigo_number_generalization_step1_328 : sin(449*pi/4)**2=cos(-pi/2) / 2 + 1 / 2:=
begin
have : cos(-pi/4) = sin(449*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/4) (56),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_number_generalization_step1_329 : -3*cos(5*pi/18) + 4*cos(5*pi/18)**3=- sqrt( 3 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_330 : -cos(3577*pi/2)=- cos(2493*pi/2):=
begin
have : sin(-pi) = -cos(3577*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (893),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - cos(2493*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (622),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_331 : -cos(11701*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(11701*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (975),
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


lemma Trigo_number_generalization_step1_332 : cos(5134*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = cos(5134*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (856),
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


lemma Trigo_number_generalization_step1_333 (h0 : sin(-3*pi/2)≠ 0) (h1 : (4*sin(-3*pi/2))≠ 0) (h2 : (2*sin((-3)*pi/2))≠ 0) : sin(pi/2) * sin(-2*pi)=cos(5*pi/2)/2 - sin(-3*pi)/(4*sin(-3*pi/2)):=
begin
have : cos(5 * pi / 2) / 2 - sin((-3) * pi) / (2 * sin((-3) * pi / 2)) / 2 = cos(5*pi/2)/2 - sin(-3*pi)/(4*sin(-3*pi/2)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi/2) * sin(-2*pi) = cos(5*pi/2) / 2 - cos(-3*pi/2) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_number_generalization_step1_334 : sin(25877*pi/18)**2=cos(-2*pi/9) / 2 + 1 / 2:=
begin
have : (-sin(25877 * pi / 18)) ** 2 = sin(25877*pi/18)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = -sin(25877*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/9) (718),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) ** 2 = cos(-2*pi/9) / 2 + 1 / 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
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


lemma Trigo_number_generalization_step1_335 : 3*sin(-pi/24) - 4*sin(-pi/24)**3=sin(6425*pi/8):=
begin
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
have : sin(-pi/8) = sin(6425*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/8) (401),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_336 : cos(1631*pi)=cos(95*pi):=
begin
have : sin(-pi/2) = cos(1631*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (815),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(95*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_337 : (1 - 2*sin(pi/2)**2)**2=cos(2*pi) / 2 + 1 / 2:=
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


lemma Trigo_number_generalization_step1_338 : -sin(pi/4)**2 + cos(pi/4)**2=- cos(3467*pi/2):=
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
have : cos(pi/2) = - cos(3467*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (866),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_339 : sin(1747*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = sin(1747*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (145),
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


lemma Trigo_number_generalization_step1_340 : sin(-pi/6) ** 2=-cos(-7*pi/3)*cos(2*pi)/2 + sin(-7*pi/3)*sin(2*pi)/2 + 1/2:=
begin
have : 1 / 2 - (-sin((-7) * pi / 3) * sin(2 * pi) + cos((-7) * pi / 3) * cos(2 * pi)) / 2 = -cos(-7*pi/3)*cos(2*pi)/2 + sin(-7*pi/3)*sin(2*pi)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -sin(-7*pi/3) * sin(2*pi) + cos(-7*pi/3) * cos(2*pi),
{
have : cos(-pi/3) = cos((-7*pi/3) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_341 : cos(2780*pi/3)=1 - 2 * sin(-pi/3) ** 2:=
begin
have : cos(-2*pi/3) = cos(2780*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi/3) (463),
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


lemma Trigo_number_generalization_step1_342 : sin(2*pi)=sin(2*pi) + sin(0):=
begin
have : 2 * (sin(0) / 2 + sin(2 * pi) / 2) = sin(2*pi) + sin(0),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * cos(pi) = sin(0) / 2 + sin(2*pi) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (pi)) = sin(2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (pi)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(pi) * cos(pi)) = 2*sin(pi)*cos(pi),
{
ring,
},
conv {to_rhs, rw this,},
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


lemma Trigo_number_generalization_step1_343 : -sin(-pi/3)*cos(3334*pi/3)=- sin(2*pi/3) / 2 + sin(0) / 2:=
begin
have : sin(-pi / 3) * -cos(3334 * pi / 3) = -sin(-pi/3)*cos(3334*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(3334*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (555),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi/3) = - sin(2*pi/3) / 2 + sin(0) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/3)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/3)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_344 : sin(3721*pi/4)=- cos(4917*pi/4):=
begin
have : cos(-pi/4) = sin(3721*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/4) (465),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - cos(4917*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (614),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_345 : tan(907*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = tan(907*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (151),
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


lemma Trigo_number_generalization_step1_346 : cos(571*pi/2)=0:=
begin
have : cos(pi/2) = cos(571*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (143),
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


lemma Trigo_number_generalization_step1_347 (h0 : cos(-pi/7)≠ 0) : (sin(-10*pi/21)*cos(-pi/3) - sin(-pi/3)*cos(-10*pi/21))/cos(-pi/7)=tan(-pi/7):=
begin
have : (sin((-10) * pi / 21) * cos(-pi / 3) - sin(-pi / 3) * cos((-10) * pi / 21)) / cos(-pi / 7) = (sin(-10*pi/21)*cos(-pi/3) - sin(-pi/3)*cos(-10*pi/21))/cos(-pi/7),
{
field_simp at *,
},
have : sin(-pi/7) = sin(-10*pi/21) * cos(-pi/3) - sin(-pi/3) * cos(-10*pi/21),
{
have : sin(-pi/7) = sin((-10*pi/21) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) / cos(-pi/7) = tan(-pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_348 : cos(-11*pi/6)=-sin(pi/6)*cos(3153*pi/2) + cos(-2*pi)*cos(pi/6):=
begin
have : -cos(3153 * pi / 2) * sin(pi / 6) + cos((-2) * pi) * cos(pi / 6) = -sin(pi/6)*cos(3153*pi/2) + cos(-2*pi)*cos(pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = cos(3153*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (787),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-11*pi/6) = - sin(-2*pi) * sin(pi/6) + cos(-2*pi) * cos(pi/6),
{
have : cos(-11*pi/6) = cos((-2*pi) + (pi/6)),
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


lemma Trigo_number_generalization_step1_349 : sin(pi/2) * sin(-pi)=sin(-5*pi/6)*sin(pi/3)/2 + cos(3*pi/2)/2 - cos(-5*pi/6)*cos(pi/3)/2:=
begin
have : cos(3 * pi / 2) / 2 - (-sin((-5) * pi / 6) * sin(pi / 3) + cos((-5) * pi / 6) * cos(pi / 3)) / 2 = sin(-5*pi/6)*sin(pi/3)/2 + cos(3*pi/2)/2 - cos(-5*pi/6)*cos(pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -sin(-5*pi/6) * sin(pi/3) + cos(-5*pi/6) * cos(pi/3),
{
have : cos(-pi/2) = cos((-5*pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) * sin(-pi) = cos(3*pi/2) / 2 - cos(-pi/2) / 2,
{
rw sin_mul_sin,
have : cos((pi/2) + (-pi)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (-pi)) = cos(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_350 : -tan(860*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(860*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (287),
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


lemma Trigo_number_generalization_step1_351 : sin(pi/3)*cos(4775*pi/6)=sin(pi/6) / 2 + sin(pi/2) / 2:=
begin
have : cos(pi/6) = cos(4775*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(pi/6) = sin(pi/6) / 2 + sin(pi/2) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (pi/6)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (pi/6)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_352 : -4*sin(pi/15)**3 + 3*sin(pi/15)=- sin(5339*pi/5):=
begin
have : (-4) * sin(pi / 15) ** 3 + 3 * sin(pi / 15) = -4*sin(pi/15)**3 + 3*sin(pi/15),
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
have : sin(pi/5) = - sin(5339*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/5) (534),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_353 : -3*cos(pi/6) + 4*cos(pi/6)**3=- cos(2201*pi/2):=
begin
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
have : cos(pi/2) = - cos(2201*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (550),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_354 (h0 : sin(pi/4)≠ 0) (h1 : (2*sin(pi/4))≠ 0) : sin(pi/2)/(2*sin(pi/4))=sqrt( 2 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_355 : -cos(2220*pi/7)=cos(4199*pi/7):=
begin
have : cos(pi/7) = -cos(2220*pi/7),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/7) (158),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = cos(4199*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/7) (300),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_356 : cos(13867*pi/18)=cos(16481*pi/18):=
begin
have : sin(pi/9) = cos(13867*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (385),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = cos(16481*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (457),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_357 (h0 : cos(-pi/4)≠ 0) : sin(-pi/4)/cos(-pi/4)=tan(1447*pi/4):=
begin
have : tan(-pi/4) = sin(-pi/4) / cos(-pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = tan(1447*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (-pi/4) (362),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_358 : cos(11*pi/6)=-(-sin(-2*pi)*cos(0) + sin(0)*cos(-2*pi))*sin(-pi/6) + cos(-pi/6)*cos(2*pi):=
begin
have : -(sin(0) * cos((-2) * pi) - sin((-2) * pi) * cos(0)) * sin(-pi / 6) + cos(2 * pi) * cos(-pi / 6) = -(-sin(-2*pi)*cos(0) + sin(0)*cos(-2*pi))*sin(-pi/6) + cos(-pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = sin(0) * cos(-2*pi) - sin(-2*pi) * cos(0),
{
have : sin(2*pi) = sin((0) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(11*pi/6) = - sin(2*pi) * sin(-pi/6) + cos(2*pi) * cos(-pi/6),
{
have : cos(11*pi/6) = cos((2*pi) + (-pi/6)),
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


lemma Trigo_number_generalization_step1_359 : -sin(7911*pi/10)=2 * cos(-pi/5) ** 2 - 1:=
begin
have : cos(-2*pi/5) = -sin(7911*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/5) (395),
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


lemma Trigo_number_generalization_step1_360 : -cos(2725*pi/4)=- sin(1005*pi/4):=
begin
have : sin(pi/4) = -cos(2725*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (340),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = - sin(1005*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (125),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_361 : cos(2633*pi/4)=cos(2729*pi/4):=
begin
have : cos(pi/4) = cos(2633*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (329),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = cos(2729*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (341),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_362 (h0 : cos(11381*pi/7)≠ 0) : sin(pi/7)/cos(11381*pi/7)=tan(pi/7):=
begin
have : cos(pi/7) = cos(11381*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/7) (813),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) / cos(pi/7) = tan(pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_363 : cos(2*pi/9)=1 - 2*cos(16873*pi/18)**2:=
begin
have : 1 - 2 * (-cos(16873 * pi / 18)) ** 2 = 1 - 2*cos(16873*pi/18)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/9) = -cos(16873*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (468),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/9) = 1 - 2 * sin(pi/9) ** 2,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
end


lemma Trigo_number_generalization_step1_364 : -cos(1588*pi)=- 1:=
begin
have : cos(pi) = -cos(1588*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (794),
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


lemma Trigo_number_generalization_step1_365 : (sin(pi/24)*cos(pi/8) + sin(pi/8)*cos(pi/24))**2=1 / 2 - cos(pi/3) / 2:=
begin
have : sin(pi/6) = sin(pi/24) * cos(pi/8) + sin(pi/8) * cos(pi/24),
{
have : sin(pi/6) = sin((pi/24) + (pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step1_366 : -tan(1873*pi/4)=- 1:=
begin
have : tan(3*pi/4) = -tan(1873*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (469),
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


lemma Trigo_number_generalization_step1_367 : -cos(5851*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -cos(5851*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (487),
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


lemma Trigo_number_generalization_step1_368 (h0 : cos(pi/6)≠ 0) : -sin(427*pi/6)/cos(pi/6)=tan(pi/6):=
begin
have : sin(pi/6) = -sin(427*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (35),
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


lemma Trigo_number_generalization_step1_369 : 1 - 2*sin(3*pi/8)**2=- sqrt( 2 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_370 : cos(3867*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = cos(3867*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/4) (483),
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


lemma Trigo_number_generalization_step1_371 : sin(1334*pi)**2=1 - cos(2*pi) ** 2:=
begin
have : sin(2*pi) = sin(1334*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (666),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) ** 2 = 1 - cos(2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_372 (h0 : tan(4691*pi/6)≠ 0) : 1/tan(4691*pi/6)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = 1 / tan(4691*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (782),
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


lemma Trigo_number_generalization_step1_373 (h0 : tan(3391*pi/4)≠ 0) : -1/tan(3391*pi/4)=1:=
begin
have : (-1) / tan(3391 * pi / 4) = -1/tan(3391*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(3391*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (847),
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


lemma Trigo_number_generalization_step1_374 : sin(5177*pi/3)*cos(-pi)=sin(2*pi/3) / 2 + sin(-4*pi/3) / 2:=
begin
have : sin(-pi/3) = sin(5177*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (863),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(-pi) = sin(2*pi/3) / 2 + sin(-4*pi/3) / 2,
{
rw sin_mul_cos,
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
},
rw this,
end


lemma Trigo_number_generalization_step1_375 : -cos(12031*pi/9)=2 * cos(pi/9) ** 2 - 1:=
begin
have : cos(2*pi/9) = -cos(12031*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/9) (668),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = 2 * cos(pi/9) ** 2 - 1,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_376 : cos(-5*pi/12)*cos(-pi/4) + sin(-5*pi/12)*sin(-pi/4)=- cos(11465*pi/6):=
begin
have : sin((-5) * pi / 12) * sin(-pi / 4) + cos((-5) * pi / 12) * cos(-pi / 4) = cos(-5*pi/12)*cos(-pi/4) + sin(-5*pi/12)*sin(-pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(-5*pi/12) * sin(-pi/4) + cos(-5*pi/12) * cos(-pi/4),
{
have : cos(-pi/6) = cos((-5*pi/12) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(11465*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (955),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_377 : sin(pi) - sin(pi/4)=2*(-1 + 2*cos(5*pi/16)**2)*sin(3*pi/8):=
begin
have : 2 * sin(3 * pi / 8) * (2 * cos(5 * pi / 16) ** 2 - 1) = 2*(-1 + 2*cos(5*pi/16)**2)*sin(3*pi/8),
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/8) = 2 * cos(5*pi/16) ** 2 - 1,
{
have : cos(5*pi/8) = cos(2*(5*pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi) - sin(pi/4) = 2 * sin(3*pi/8) * cos(5*pi/8),
{
rw sin_sub_sin,
have : cos(((pi) + (pi/4))/2) = cos(5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi) - (pi/4))/2) = sin(3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_378 : sin(6133*pi/6)=1 / 2:=
begin
have : cos(pi/3) = sin(6133*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (511),
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


lemma Trigo_number_generalization_step1_379 : cos(-pi/9)=-cos(10432*pi/9):=
begin
have : sin(17759*pi/18) = -cos(10432*pi/9),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (17759*pi/18) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = sin(17759*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/9) (493),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_380 : -cos(4013*pi/4)=- cos(2605*pi/4):=
begin
have : sin(pi/4) = -cos(4013*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (501),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = - cos(2605*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (325),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_381 : sin(pi)=cos(289*pi/2):=
begin
have : - -cos(289 * pi / 2) = cos(289*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3365*pi/2) = -cos(289*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3365*pi/2) (913),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = - cos(3365*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (841),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_382 : -4*sin(pi/3)**3 + 3*sin(pi/3)=- cos(1621*pi/2):=
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
have : sin(pi) = - cos(1621*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (405),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_383 : -1 + 2*sin(-pi/18)**2 + cos(pi/3)=- 2 * sin(2*pi/9) * sin(pi/9):=
begin
have : cos(pi / 3) - (1 - 2 * sin(-pi / 18) ** 2) = -1 + 2*sin(-pi/18)**2 + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = 1 - 2 * sin(-pi/18) ** 2,
{
have : cos(-pi/9) = cos(2*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) - cos(-pi/9) = - 2 * sin(2*pi/9) * sin(pi/9),
{
rw cos_sub_cos,
have : sin(((pi/3) + (-pi/9))/2) = sin(pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (-pi/9))/2) = sin(2*pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_384 (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) : 2*tan(pi/12)/(1 - tan(pi/12)**2)=sin(pi/6) / cos(pi/6):=
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
have : tan(pi/6) = sin(pi/6) / cos(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_385 (h0 : tan(1529*pi/2)≠ 0) : -1/tan(1529*pi/2)=- 1 / tan(373*pi/2):=
begin
have : (-1) / tan(1529 * pi / 2) = -1/tan(1529*pi/2),
{
field_simp at *,
},
have : tan(pi) = -1 / tan(1529*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (763),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - 1 / tan(373*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (185),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_386 : -sin(11017*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = -sin(11017*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (917),
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


lemma Trigo_number_generalization_step1_387 : cos(pi/8)=-sin(14285*pi/8):=
begin
have : sin(11813*pi/8) = -sin(14285*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (11813*pi/8) (154),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = sin(11813*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/8) (738),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_388 : -cos(-pi/6) + cos(194*pi)=- 2 * sin(13*pi/12) * sin(11*pi/12):=
begin
have : cos(194 * pi) - cos(-pi / 6) = -cos(-pi/6) + cos(194*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(194*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_389 : -sin(pi/5)*cos(11*pi/30) + sin(11*pi/30)*cos(pi/5)=sin(10253*pi/6):=
begin
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
have : sin(pi/6) = sin(10253*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (854),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_390 : cos(17*pi/8)=-sin(2*pi)*cos(1587*pi/8) + cos(-pi/8)*cos(2*pi):=
begin
have : sin(2 * pi) * -cos(1587 * pi / 8) + cos(2 * pi) * cos(-pi / 8) = -sin(2*pi)*cos(1587*pi/8) + cos(-pi/8)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) = -cos(1587*pi/8),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/8) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(17*pi/8) = sin(2*pi) * sin(-pi/8) + cos(2*pi) * cos(-pi/8),
{
have : cos(17*pi/8) = cos((2*pi) - (-pi/8)),
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


lemma Trigo_number_generalization_step1_391 : -tan(9227*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(pi/12) = -tan(9227*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (769),
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


lemma Trigo_number_generalization_step1_392 : cos(3277*pi/2)=2 * sin(-2*pi) * cos(-2*pi):=
begin
have : sin(-4*pi) = cos(3277*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-4*pi) (817),
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


lemma Trigo_number_generalization_step1_393 : 2*sin(pi/8)*cos(pi/8)=sqrt( 2 ) / 2:=
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
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_394 (h0 : cos(8*pi/3)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (tan(2*pi)*tan(8*pi/3)+1)≠ 0) (h3 : (1+tan(8*pi/3)*tan(2*pi))≠ 0) : (tan(8*pi/3) - tan(2*pi))/(tan(2*pi)*tan(8*pi/3) + 1)=- sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_395 : sin(-pi/5)*cos(17*pi/60) + sin(17*pi/60)*cos(-pi/5)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(17 * pi / 60) * cos(-pi / 5) + sin(-pi / 5) * cos(17 * pi / 60) = sin(-pi/5)*cos(17*pi/60) + sin(17*pi/60)*cos(-pi/5),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(17*pi/60) * cos(-pi/5) + sin(-pi/5) * cos(17*pi/60),
{
have : sin(pi/12) = sin((17*pi/60) + (-pi/5)),
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


lemma Trigo_number_generalization_step1_396 : sin(2885*pi/2)*cos(-pi/9)=cos(-19*pi/9) / 2 + cos(17*pi/9) / 2:=
begin
have : cos(-pi / 9) * sin(2885 * pi / 2) = sin(2885*pi/2)*cos(-pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(2885*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (722),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) * cos(2*pi) = cos(-19*pi/9) / 2 + cos(17*pi/9) / 2,
{
rw cos_mul_cos,
have : cos((-pi/9) + (2*pi)) = cos(17*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/9) - (2*pi)) = cos(-19*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_397 : (-sin(-pi/4)**2 + cos(-pi/4)**2)*sin(pi/6)=- sin(-2*pi/3) / 2 + sin(-pi/3) / 2:=
begin
have : sin(pi / 6) * (-sin(-pi / 4) ** 2 + cos(-pi / 4) ** 2) = (-sin(-pi/4)**2 + cos(-pi/4)**2)*sin(pi/6),
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
have : sin(pi/6) * cos(-pi/2) = - sin(-2*pi/3) / 2 + sin(-pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (pi/6)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (pi/6)) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_398 (h0 : cos((-4*pi)/2)≠ 0) (h1 : (1+cos((-4)*pi))≠ 0) (h2 : (1+cos(-4*pi))≠ 0) : sin(-4*pi)/(1 + cos(-4*pi))=tan(172*pi):=
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
have : tan(-2*pi) = tan(172*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (174),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_399 (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) : -sin(83*pi)/cos(-2*pi)=tan(-2*pi):=
begin
have : -sin(83 * pi) / cos((-2) * pi) = -sin(83*pi)/cos(-2*pi),
{
field_simp at *,
},
have : sin(-2*pi) = -sin(83*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (42),
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


lemma Trigo_number_generalization_step1_400 : cos(pi/9) ** 2=1 - (-4*sin(pi/27)**3 + 3*sin(pi/27))**2:=
begin
have : 1 - ((-4) * sin(pi / 27) ** 3 + 3 * sin(pi / 27)) ** 2 = 1 - (-4*sin(pi/27)**3 + 3*sin(pi/27))**2,
{
field_simp at *,
},
have : sin(pi/9) = -4 * sin(pi/27) ** 3 + 3 * sin(pi/27),
{
have : sin(pi/9) = sin(3*(pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) ** 2 = 1 - sin(pi/9) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_401 (h0 : tan(715*pi/4)≠ 0) : 1/tan(715*pi/4)=- 1:=
begin
have : tan(3*pi/4) = 1 / tan(715*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (179),
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


lemma Trigo_number_generalization_step1_402 : -tan(267*pi/2)=- 1 / tan(340*pi):=
begin
have : tan(-pi/2) = -tan(267*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (133),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - 1 / tan(340*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (340),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_403 : tan(1073*pi/6)=1 / tan(1790*pi/3):=
begin
have : tan(-pi/6) = tan(1073*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (179),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = 1 / tan(1790*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (596),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_404 : -sin(-pi/3)*sin(1429*pi)=cos(-7*pi/3) / 2 - cos(5*pi/3) / 2:=
begin
have : sin(-pi / 3) * -sin(1429 * pi) = -sin(-pi/3)*sin(1429*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(1429*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (713),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * sin(2*pi) = cos(-7*pi/3) / 2 - cos(5*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((-pi/3) + (2*pi)) = cos(5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/3) - (2*pi)) = cos(-7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_405 : -cos(7223*pi/4)=sin(6397*pi/4):=
begin
have : sin(-pi/4) = -cos(7223*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (902),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(6397*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/4) (799),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_406 : 4*sin(-pi/4)**2*cos(-pi/4)**2=1 / 2 - cos(-pi) / 2:=
begin
have : (2 * sin(-pi / 4) * cos(-pi / 4)) ** 2 = 4*sin(-pi/4)**2*cos(-pi/4)**2,
{
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


lemma Trigo_number_generalization_step1_407 (h0 : sin(-pi/6)≠ 0) (h1 : (2*sin(-pi/6))≠ 0) : sin(-pi/3)/(2*sin(-pi/6))=- sin(53*pi/3):=
begin
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
have : cos(-pi/6) = - sin(53*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_408 : -sin(1100*pi)=sin(1660*pi):=
begin
have : sin(pi) = -sin(1100*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (549),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(1660*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (830),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_409 : -tan(959*pi/4)=1:=
begin
have : tan(pi/4) = -tan(959*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (240),
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


lemma Trigo_number_generalization_step1_410 : sin(pi/12)*cos(-pi/6) - sin(-pi/6)*cos(pi/12)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = sin(pi/12) * cos(-pi/6) - sin(-pi/6) * cos(pi/12),
{
have : sin(pi/4) = sin((pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_411 : cos(8441*pi/7)**2=cos(2*pi/7) / 2 + 1 / 2:=
begin
have : cos(pi/7) = cos(8441*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/7) (603),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) ** 2 = cos(2*pi/7) / 2 + 1 / 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
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


lemma Trigo_number_generalization_step1_412 : sin(13701*pi/14)**2=cos(-2*pi/7) / 2 + 1 / 2:=
begin
have : cos(-pi/7) = sin(13701*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (489),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_number_generalization_step1_413 : sin(2036*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = sin(2036*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (339),
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


lemma Trigo_number_generalization_step1_414 : sin(-pi/6)=-cos(4993*pi/3):=
begin
have : cos(400*pi/3) = -cos(4993*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (400*pi/3) (765),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = cos(400*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_415 (h0 : cos((-pi)/2)≠ 0) (h1 : sin(-pi)≠ 0) : (1 - cos(-pi))/sin(-pi)=- tan(287*pi/2):=
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
have : tan(-pi/2) = - tan(287*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (143),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_416 : sin(2*pi)=2*(cos(-2*pi)*cos(3*pi) - sin(-2*pi)*sin(3*pi))*sin(pi):=
begin
have : 2 * sin(pi) * (-sin(3 * pi) * sin((-2) * pi) + cos(3 * pi) * cos((-2) * pi)) = 2*(cos(-2*pi)*cos(3*pi) - sin(-2*pi)*sin(3*pi))*sin(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -sin(3*pi) * sin(-2*pi) + cos(3*pi) * cos(-2*pi),
{
have : cos(pi) = cos((3*pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_417 : -cos(1931*pi)=1:=
begin
have : sin(pi/2) = -cos(1931*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (965),
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


lemma Trigo_number_generalization_step1_418 : cos(5087*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = cos(5087*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (635),
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


lemma Trigo_number_generalization_step1_419 (h0 : tan(37*pi/8)≠ 0) : 1/tan(37*pi/8)=- tan(1513*pi/8):=
begin
have : tan(-pi/8) = 1 / tan(37*pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/8) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - tan(1513*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (189),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_420 (h0 : cos(3*pi/4)≠ 0) (h1 : (2*cos(3*pi/4))≠ 0) : sin(3*pi/2)/(2*cos(3*pi/4))=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(3*pi/2) / ( 2 * cos(3*pi/4) ),
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
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_421 (h0 : tan(5115*pi/8)≠ 0) : -1/tan(5115*pi/8)=- tan(4713*pi/8):=
begin
have : (-1) / tan(5115 * pi / 8) = -1/tan(5115*pi/8),
{
field_simp at *,
},
have : tan(-pi/8) = -1 / tan(5115*pi/8),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/8) (639),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - tan(4713*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (589),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_422 (h0 : (-sin(-pi/5)*sin(3*pi/40)+cos(-pi/5)*cos(3*pi/40))≠ 0) (h1 : (-sin(3*pi/40)*sin(-pi/5)+cos(3*pi/40)*cos(-pi/5))≠ 0) : tan(-pi/8)=sin(-pi/8)/(-sin(-pi/5)*sin(3*pi/40) + cos(-pi/5)*cos(3*pi/40)):=
begin
have : sin(-pi / 8) / (-sin(3 * pi / 40) * sin(-pi / 5) + cos(3 * pi / 40) * cos(-pi / 5)) = sin(-pi/8)/(-sin(-pi/5)*sin(3*pi/40) + cos(-pi/5)*cos(3*pi/40)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = -sin(3*pi/40) * sin(-pi/5) + cos(3*pi/40) * cos(-pi/5),
{
have : cos(-pi/8) = cos((3*pi/40) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/8) = sin(-pi/8) / cos(-pi/8),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_423 : sin(7*pi/24)=-sin(pi/8)*sin(1757*pi/3) + sin(pi/6)*cos(pi/8):=
begin
have : sin(pi / 8) * -sin(1757 * pi / 3) + sin(pi / 6) * cos(pi / 8) = -sin(pi/8)*sin(1757*pi/3) + sin(pi/6)*cos(pi/8),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -sin(1757*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (292),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(7*pi/24) = sin(pi/8) * cos(pi/6) + sin(pi/6) * cos(pi/8),
{
have : sin(7*pi/24) = sin((pi/8) + (pi/6)),
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


lemma Trigo_number_generalization_step1_424 : -cos(7239*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -cos(7239*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3*pi/4) (904),
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


lemma Trigo_number_generalization_step1_425 : -cos(15439*pi/8)=sin(pi/8) * sin(-pi) + cos(pi/8) * cos(-pi):=
begin
have : cos(9*pi/8) = -cos(15439*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (9*pi/8) (965),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(9*pi/8) = sin(pi/8) * sin(-pi) + cos(pi/8) * cos(-pi),
{
have : cos(9*pi/8) = cos((pi/8) - (-pi)),
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


lemma Trigo_number_generalization_step1_426 : -cos(340*pi)=- cos(1642*pi):=
begin
have : cos(-pi) = -cos(340*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (169),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(1642*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (821),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_427 : -4*sin(pi/3)**3 + 3*sin(pi/3)=0:=
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_428 : cos(14559*pi/8)=- cos(11575*pi/8):=
begin
have : cos(pi/8) = cos(14559*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/8) (910),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = - cos(11575*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/8) (723),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_429 (h0 : cos(5*pi/6)≠ 0) (h1 : (2*cos(5*pi/6))≠ 0) : sin(5*pi/3)/(2*cos(5*pi/6))=1 / 2:=
begin
have : sin(5*pi/6) = sin(5*pi/3) / ( 2 * cos(5*pi/6) ),
{
have : sin(5*pi/3) = sin(2*(5*pi/6)),
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
have : sin(5*pi/6) = 1 / 2,
{
rw sin_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_430 : cos(4*pi/5)=cos(pi/5)*cos(pi) + sin(pi/5)*cos(1039*pi/2):=
begin
have : cos(1039 * pi / 2) * sin(pi / 5) + cos(pi) * cos(pi / 5) = cos(pi/5)*cos(pi) + sin(pi/5)*cos(1039*pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = cos(1039*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (260),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi/5) = sin(pi) * sin(pi/5) + cos(pi) * cos(pi/5),
{
have : cos(4*pi/5) = cos((pi) - (pi/5)),
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


lemma Trigo_number_generalization_step1_431 : cos(15751*pi/10)=- 4 * sin(-pi/5) ** 3 + 3 * sin(-pi/5):=
begin
have : sin(-3*pi/5) = cos(15751*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-3*pi/5) (787),
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


lemma Trigo_number_generalization_step1_432 : cos(285*pi/2)=0:=
begin
have : cos(pi/2) = cos(285*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (71),
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


lemma Trigo_number_generalization_step1_433 : sin(12735*pi/14)=- sin(pi/7) * sin(pi) + cos(pi/7) * cos(pi):=
begin
have : cos(8*pi/7) = sin(12735*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (8*pi/7) (454),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi/7) = - sin(pi/7) * sin(pi) + cos(pi/7) * cos(pi),
{
have : cos(8*pi/7) = cos((pi/7) + (pi)),
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


lemma Trigo_number_generalization_step1_434 : sin(327*pi/2)=4 * cos(pi/3) ** 3 - 3 * cos(pi/3):=
begin
have : cos(pi) = sin(327*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (81),
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


lemma Trigo_number_generalization_step1_435 : sin(11*pi/12)*cos(pi/4) - sin(pi/4)*cos(11*pi/12)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = sin(11*pi/12) * cos(pi/4) - sin(pi/4) * cos(11*pi/12),
{
have : sin(2*pi/3) = sin((11*pi/12) - (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_436 : 2*sin(-pi/6)*cos(-pi/6) - sin(-2*pi)=2 * sin(5*pi/6) * cos(-7*pi/6):=
begin
have : 2 * sin(-pi / 6) * cos(-pi / 6) - sin((-2) * pi) = 2*sin(-pi/6)*cos(-pi/6) - sin(-2*pi),
{
field_simp at *,
},
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
have : sin(-pi/3) - sin(-2*pi) = 2 * sin(5*pi/6) * cos(-7*pi/6),
{
rw sin_sub_sin,
have : cos(((-pi/3) + (-2*pi))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (-2*pi))/2) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_437 : sin(6941*pi/6)=- cos(4960*pi/3):=
begin
have : cos(pi/3) = sin(6941*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (578),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - cos(4960*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (826),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_438 (h0 : cos((-pi)/2)≠ 0) (h1 : sin(-pi)≠ 0) : (1 - cos(-pi))/sin(-pi)=tan(265*pi/2):=
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
have : tan(-pi/2) = tan(265*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (-pi/2) (133),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_439 (h0 : tan(2770*pi/3)≠ 0) : 1/tan(2770*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(2770*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (923),
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


lemma Trigo_number_generalization_step1_440 : -1 + 2*cos(pi/8)**2=sqrt( 2 ) / 2:=
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_441 : sin(1987*pi)**2=cos(-pi) / 2 + 1 / 2:=
begin
have : (-sin(1987 * pi)) ** 2 = sin(1987*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(1987*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (993),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) ** 2 = cos(-pi) / 2 + 1 / 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
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


lemma Trigo_number_generalization_step1_442 : cos(2*pi/5)=1 - 2*sin(pi/5)**2:=
begin
have : 2 * (1 - sin(pi / 5) ** 2) - 1 = 1 - 2*sin(pi/5)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) ** 2 = 1 - sin(pi/5) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step1_443 (h0 : cos(-pi/7)≠ 0) : sin(13798*pi/7)/cos(-pi/7)=tan(-pi/7):=
begin
have : sin(-pi/7) = sin(13798*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/7) (985),
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


lemma Trigo_number_generalization_step1_444 : -cos(1777*pi/2)=- cos(1145*pi/2):=
begin
have : sin(2*pi) = -cos(1777*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (443),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(1145*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (285),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_445 : cos(9691*pi/18)=- sin(15130*pi/9):=
begin
have : sin(pi/9) = cos(9691*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (269),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = - sin(15130*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/9) (840),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_446 : -sin(6615*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = -sin(6615*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (826),
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


lemma Trigo_number_generalization_step1_447 : -cos(2519*pi/2)=0:=
begin
have : sin(pi) = -cos(2519*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (629),
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


lemma Trigo_number_generalization_step1_448 : -tan(3087*pi/4)=1:=
begin
have : tan(pi/4) = -tan(3087*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (772),
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


lemma Trigo_number_generalization_step1_449 : (1 - 2*sin(-pi/8)**2)*sin(-pi/8)=sin(pi/8) / 2 + sin(-3*pi/8) / 2:=
begin
have : sin(-pi / 8) * (1 - 2 * sin(-pi / 8) ** 2) = (1 - 2*sin(-pi/8)**2)*sin(-pi/8),
{
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
have : sin(-pi/8) * cos(-pi/4) = sin(pi/8) / 2 + sin(-3*pi/8) / 2,
{
rw sin_mul_cos,
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
},
rw this,
end


lemma Trigo_number_generalization_step1_450 : -sin(3461*pi/4)=- cos(4189*pi/4):=
begin
have : sin(pi/4) = -sin(3461*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (432),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = - cos(4189*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (523),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_451 : sin(pi/9)=1 - 2*cos(2387*pi/36)**2:=
begin
have : -(2 * cos(2387 * pi / 36) ** 2 - 1) = 1 - 2*cos(2387*pi/36)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2387*pi/18) = 2 * cos(2387*pi/36) ** 2 - 1,
{
have : cos(2387*pi/18) = cos(2*(2387*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/9) = - cos(2387*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/9) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_452 (h0 : sin(2*pi/3)≠ 0) (h1 : (2*sin(2*pi/3))≠ 0) : sin(4*pi/3)/(2*sin(2*pi/3))=- 1 / 2:=
begin
have : cos(2*pi/3) = sin(4*pi/3) / ( 2 * sin(2*pi/3) ),
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
have : cos(2*pi/3) = - 1 / 2,
{
rw cos_two_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_453 (h0 : tan(1483*pi/6)≠ 0) : -1/tan(1483*pi/6)=- 1 / tan(763*pi/6):=
begin
have : (-1) / tan(1483 * pi / 6) = -1/tan(1483*pi/6),
{
field_simp at *,
},
have : tan(-pi/3) = -1 / tan(1483*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (247),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - 1 / tan(763*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (127),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_454 : -cos(769*pi/2)=- cos(3085*pi/2):=
begin
have : sin(-pi) = -cos(769*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (191),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - cos(3085*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (770),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_455 : -sin(939*pi)=- 4 * sin(pi/3) ** 3 + 3 * sin(pi/3):=
begin
have : sin(pi) = -sin(939*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (470),
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


lemma Trigo_number_generalization_step1_456 (h0 : tan(361*pi/2)≠ 0) : -1/tan(361*pi/2)=1 / tan(415*pi/2):=
begin
have : (-1) / tan(361 * pi / 2) = -1/tan(361*pi/2),
{
field_simp at *,
},
have : tan(-pi) = -1 / tan(361*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (181),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = 1 / tan(415*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (206),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_457 (h0 : tan(2195*pi/6)≠ 0) : 1/tan(2195*pi/6)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = 1 / tan(2195*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (366),
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


lemma Trigo_number_generalization_step1_458 : -cos(793*pi)=cos(844*pi):=
begin
have : sin(pi/2) = -cos(793*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (396),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(844*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (422),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_459 : sin(11*pi/6)*cos(pi/6) + sin(pi/6)*cos(11*pi/6)=- cos(2777*pi/2):=
begin
have : sin(2*pi) = sin(11*pi/6) * cos(pi/6) + sin(pi/6) * cos(11*pi/6),
{
have : sin(2*pi) = sin((11*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(2777*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (693),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_460 : 1 - 2*sin(-pi/7)**2=2 * cos(-pi/7) ** 2 - 1:=
begin
have : cos(-2*pi/7) = 1 - 2 * sin(-pi/7) ** 2,
{
have : cos(-2*pi/7) = cos(2*(-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
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
rw this,
end


lemma Trigo_number_generalization_step1_461 : sin(9*pi/14)=-sin(-pi/7)*cos(pi/2) + (-sin(-pi/14)**2 + cos(-pi/14)**2)*sin(pi/2):=
begin
have : sin(pi / 2) * (-sin(-pi / 14) ** 2 + cos(-pi / 14) ** 2) - sin(-pi / 7) * cos(pi / 2) = -sin(-pi/7)*cos(pi/2) + (-sin(-pi/14)**2 + cos(-pi/14)**2)*sin(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(9*pi/14) = sin(pi/2) * cos(-pi/7) - sin(-pi/7) * cos(pi/2),
{
have : sin(9*pi/14) = sin((pi/2) - (-pi/7)),
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


lemma Trigo_number_generalization_step1_462 : sin(-pi/2) + sin(-pi/3)=2*(-sin(-pi/24)**2 + cos(-pi/24)**2)*sin(-5*pi/12):=
begin
have : 2 * sin((-5) * pi / 12) * (-sin(-pi / 24) ** 2 + cos(-pi / 24) ** 2) = 2*(-sin(-pi/24)**2 + cos(-pi/24)**2)*sin(-5*pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-pi/2) + sin(-pi/3) = 2 * sin(-5*pi/12) * cos(-pi/12),
{
rw sin_add_sin,
have : sin(((-pi/2) + (-pi/3))/2) = sin(-5*pi/12),
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
},
rw this,
end


lemma Trigo_number_generalization_step1_463 (h0 : tan(10925*pi/12)≠ 0) : 1/tan(10925*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(pi/12) = 1 / tan(10925*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (910),
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


lemma Trigo_number_generalization_step1_464 : -sin(11050*pi/7)=- 4 * sin(-pi/7) ** 3 + 3 * sin(-pi/7):=
begin
have : sin(-3*pi/7) = -sin(11050*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-3*pi/7) (789),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/7) = - 4 * sin(-pi/7) ** 3 + 3 * sin(-pi/7),
{
have : sin(-3*pi/7) = sin(3*(-pi/7)),
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


lemma Trigo_number_generalization_step1_465 : tan(5839*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = tan(5839*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (973),
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


lemma Trigo_number_generalization_step1_466 : -cos(2086*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(2086*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (347),
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


lemma Trigo_number_generalization_step1_467 : -sin(pi/3)*cos(pi/2) + sin(pi/2)*cos(pi/3)=1 / 2:=
begin
have : sin(pi / 2) * cos(pi / 3) - sin(pi / 3) * cos(pi / 2) = -sin(pi/3)*cos(pi/2) + sin(pi/2)*cos(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(pi/2) * cos(pi/3) - sin(pi/3) * cos(pi/2),
{
have : sin(pi/6) = sin((pi/2) - (pi/3)),
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


lemma Trigo_number_generalization_step1_468 (h0 : cos(pi/5)≠ 0) : cos(7757*pi/10)/cos(pi/5)=tan(pi/5):=
begin
have : sin(pi/5) = cos(7757*pi/10),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (387),
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


lemma Trigo_number_generalization_step1_469 : -tan(1798*pi/3)=1 / tan(419*pi/6):=
begin
have : tan(-pi/3) = -tan(1798*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (599),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = 1 / tan(419*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_470 (h0 : sin(pi/3)≠ 0) (h1 : (2*sin(pi/3))≠ 0) : sin(2*pi/3)/(2*sin(pi/3))=1 / 2:=
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_471 : sin(-pi/4)=2*sin(-pi/8)*cos(11777*pi/8):=
begin
have : cos(-pi/8) = cos(11777*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/8) (736),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) = 2 * sin(-pi/8) * cos(-pi/8),
{
have : sin(-pi/4) = sin(2*(-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_472 : sin(-pi/12)*cos(-pi/6) - sin(-pi/6)*cos(-pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = sin(-pi/12) * cos(-pi/6) - sin(-pi/6) * cos(-pi/12),
{
have : sin(pi/12) = sin((-pi/12) - (-pi/6)),
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


lemma Trigo_number_generalization_step1_473 : cos(2*pi)=-cos(1131*pi/2)**2 + cos(pi)**2:=
begin
have : -(-cos(1131 * pi / 2)) ** 2 + cos(pi) ** 2 = -cos(1131*pi/2)**2 + cos(pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -cos(1131*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (282),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_474 : -cos(2581*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(2581*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (215),
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


lemma Trigo_number_generalization_step1_475 : sin(1453*pi/2)=1:=
begin
have : sin(pi/2) = sin(1453*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (363),
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


lemma Trigo_number_generalization_step1_476 : sin(5186*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(5186*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (864),
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


lemma Trigo_number_generalization_step1_477 : sin(pi/4)*cos(-3*pi/4) + sin(-3*pi/4)*cos(pi/4)=- sin(1601*pi/2):=
begin
have : sin((-3) * pi / 4) * cos(pi / 4) + sin(pi / 4) * cos((-3) * pi / 4) = sin(pi/4)*cos(-3*pi/4) + sin(-3*pi/4)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-3*pi/4) * cos(pi/4) + sin(pi/4) * cos(-3*pi/4),
{
have : sin(-pi/2) = sin((-3*pi/4) + (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(1601*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (400),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_478 : sin(-pi)=-3*cos(2353*pi/6) + 4*cos(2353*pi/6)**3:=
begin
have : 4 * cos(2353 * pi / 6) ** 3 - 3 * cos(2353 * pi / 6) = -3*cos(2353*pi/6) + 4*cos(2353*pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2353*pi/2) = 4 * cos(2353*pi/6) ** 3 - 3 * cos(2353*pi/6),
{
have : cos(2353*pi/2) = cos(3*(2353*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(2353*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (588),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_479 : sin(pi/4) * sin(pi)=cos(2787*pi/4)/2 - cos(5*pi/4)/2:=
begin
have : cos(-3*pi/4) = cos(2787*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-3*pi/4) (348),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) * sin(pi) = cos(-3*pi/4) / 2 - cos(5*pi/4) / 2,
{
rw sin_mul_sin,
have : cos((pi/4) + (pi)) = cos(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/4) - (pi)) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_480 : -cos(12971*pi/8)=4 * cos(-pi/8) ** 3 - 3 * cos(-pi/8):=
begin
have : cos(-3*pi/8) = -cos(12971*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3*pi/8) (810),
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


lemma Trigo_number_generalization_step1_481 : -tan(8867*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(pi/12) = -tan(8867*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (739),
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


lemma Trigo_number_generalization_step1_482 : -cos(6759*pi/8) + cos(2*pi)=2 * cos(-15*pi/16) * cos(17*pi/16):=
begin
have : cos(pi/8) = -cos(6759*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/8) (422),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) + cos(2*pi) = 2 * cos(-15*pi/16) * cos(17*pi/16),
{
rw cos_add_cos,
have : cos(((pi/8) + (2*pi))/2) = cos(17*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/8) - (2*pi))/2) = cos(-15*pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_483 : sin(-pi/2) ** 2=1/2 + sin(2125*pi/2)/2:=
begin
have : 1 / 2 - -sin(2125 * pi / 2) / 2 = 1/2 + sin(2125*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -sin(2125*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (530),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_484 : cos(pi/5)*cos(6*pi/5) + sin(pi/5)*sin(6*pi/5)=sin(3763*pi/2):=
begin
have : sin(6 * pi / 5) * sin(pi / 5) + cos(6 * pi / 5) * cos(pi / 5) = cos(pi/5)*cos(6*pi/5) + sin(pi/5)*sin(6*pi/5),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(6*pi/5) * sin(pi/5) + cos(6*pi/5) * cos(pi/5),
{
have : cos(pi) = cos((6*pi/5) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(3763*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (940),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_485 : -cos(-pi/2)*cos(1342*pi)=cos(-pi/2) / 2 + cos(-3*pi/2) / 2:=
begin
have : -cos(1342 * pi) * cos(-pi / 2) = -cos(-pi/2)*cos(1342*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -cos(1342*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (671),
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


lemma Trigo_number_generalization_step1_486 : (1 - 2*sin(pi/8)**2)**2 + sin(pi/4)**2=1:=
begin
have : sin(pi / 4) ** 2 + (1 - 2 * sin(pi / 8) ** 2) ** 2 = (1 - 2*sin(pi/8)**2)**2 + sin(pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi/4) ** 2 + cos(pi/4) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_487 : -sin(506*pi)=- cos(1235*pi/2):=
begin
have : cos(-pi/2) = -sin(506*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (252),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(1235*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (308),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_488 : sin(2063*pi/2)=- sin(1317*pi/2):=
begin
have : sin(-pi/2) = sin(2063*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (516),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(1317*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (329),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_489 (h0 : cos(-pi/8)≠ 0) : sin(-pi/8)/cos(-pi/8)=- tan(3073*pi/8):=
begin
have : tan(-pi/8) = sin(-pi/8) / cos(-pi/8),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - tan(3073*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (384),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_490 : -cos(713*pi/10)=- cos(19727*pi/10):=
begin
have : sin(pi/5) = -cos(713*pi/10),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = - cos(19727*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/5) (986),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_491 : -sin(-pi/12)**2 + cos(-pi/2) + cos(-pi/12)**2=2 * cos(pi/6) * cos(-pi/3):=
begin
have : -sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2 + cos(-pi / 2) = -sin(-pi/12)**2 + cos(-pi/2) + cos(-pi/12)**2,
{
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
have : cos(-pi/6) + cos(-pi/2) = 2 * cos(pi/6) * cos(-pi/3),
{
rw cos_add_cos,
have : cos(((-pi/6) + (-pi/2))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (-pi/2))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_492 : sin(5789*pi/6)=1 / 2:=
begin
have : sin(pi/6) = sin(5789*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (482),
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


lemma Trigo_number_generalization_step1_493 : -sin(3*pi/4)**2 + cos(3*pi/4)**2=4 * cos(pi/2) ** 3 - 3 * cos(pi/2):=
begin
have : cos(3*pi/2) = -sin(3*pi/4) ** 2 + cos(3*pi/4) ** 2,
{
have : cos(3*pi/2) = cos(2*(3*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
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


lemma Trigo_number_generalization_step1_494 : cos(13385*pi/8)=- 4 * sin(-pi/8) ** 3 + 3 * sin(-pi/8):=
begin
have : sin(-3*pi/8) = cos(13385*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/8) (836),
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


lemma Trigo_number_generalization_step1_495 : sin(-2*pi) + sin(202*pi)=2 * sin(0) * cos(2*pi):=
begin
have : sin(202 * pi) + sin((-2) * pi) = sin(-2*pi) + sin(202*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(202*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_496 : -sin(pi/4)*cos(pi/12) + sin(pi/12)*cos(pi/4)=sin(4559*pi/6):=
begin
have : sin(pi / 12) * cos(pi / 4) - sin(pi / 4) * cos(pi / 12) = -sin(pi/4)*cos(pi/12) + sin(pi/12)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(pi/12) * cos(pi/4) - sin(pi/4) * cos(pi/12),
{
have : sin(-pi/6) = sin((pi/12) - (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(4559*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (380),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_497 (h0 : cos(-pi/6)≠ 0) : -cos(3101*pi/3)/cos(-pi/6)=tan(-pi/6):=
begin
have : sin(-pi/6) = -cos(3101*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (516),
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


lemma Trigo_number_generalization_step1_498 : cos(pi/5)=-sin(-pi/6)*cos(12818*pi/15) + sin(12818*pi/15)*cos(-pi/6):=
begin
have : sin(12818 * pi / 15) * cos(-pi / 6) - sin(-pi / 6) * cos(12818 * pi / 15) = -sin(-pi/6)*cos(12818*pi/15) + sin(12818*pi/15)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(8547*pi/10) = sin(12818*pi/15) * cos(-pi/6) - sin(-pi/6) * cos(12818*pi/15),
{
have : sin(8547*pi/10) = sin((12818*pi/15) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/5) = sin(8547*pi/10),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/5) (427),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_499 : sin(1823*pi)**2=1 - cos(-pi) ** 2:=
begin
have : (-sin(1823 * pi)) ** 2 = sin(1823*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -sin(1823*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (911),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) ** 2 = 1 - cos(-pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_500 : cos(pi/3)=sin(5540*pi/3)*cos(pi/2) - sin(pi/2)*cos(5540*pi/3):=
begin
have : sin(11077*pi/6) = sin(5540*pi/3) * cos(pi/2) - sin(pi/2) * cos(5540*pi/3),
{
have : sin(11077*pi/6) = sin((5540*pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(11077*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (923),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_501 : sin(2041*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = sin(2041*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (340),
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


lemma Trigo_number_generalization_step1_502 : -sin(3*pi/2)**2 + cos(3*pi/2)**2=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : cos(3*pi) = -sin(3*pi/2) ** 2 + cos(3*pi/2) ** 2,
{
have : cos(3*pi) = cos(2*(3*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
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


lemma Trigo_number_generalization_step1_503 : -tan(1863*pi/2)=- 1 / tan(377*pi):=
begin
have : tan(-pi/2) = -tan(1863*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (931),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - 1 / tan(377*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (377),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_504 : -cos(2449*pi/2)=- sin(855*pi):=
begin
have : sin(-pi) = -cos(2449*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (611),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(855*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (427),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_505 : -sin(2357*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -sin(2357*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (392),
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


lemma Trigo_number_generalization_step1_506 : cos(3361*pi/3)=- sin(767*pi/6):=
begin
have : sin(pi/6) = cos(3361*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (560),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(767*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_507 : sin(-pi)*cos(3*pi/2) + sin(3*pi/2)*cos(-pi)=- sin(919*pi/2):=
begin
have : sin(3 * pi / 2) * cos(-pi) + sin(-pi) * cos(3 * pi / 2) = sin(-pi)*cos(3*pi/2) + sin(3*pi/2)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(919*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (229),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_508 : sin(-pi/2)*sin(pi/2) + cos(-pi/2)*cos(pi/2)=- cos(1288*pi):=
begin
have : sin(pi / 2) * sin(-pi / 2) + cos(pi / 2) * cos(-pi / 2) = sin(-pi/2)*sin(pi/2) + cos(-pi/2)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(1288*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (644),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_509 : sin(3763*pi/2)=- 1:=
begin
have : cos(pi) = sin(3763*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (941),
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


lemma Trigo_number_generalization_step1_510 : cos(-pi/9)=-cos(11330*pi/9):=
begin
have : sin(763*pi/18) = -cos(11330*pi/9),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (763*pi/18) (608),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = sin(763*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_511 : -cos(2902*pi/3)=1 / 2:=
begin
have : sin(5*pi/6) = -cos(2902*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (483),
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


lemma Trigo_number_generalization_step1_512 : -sin(5499*pi/8)=- sin(11901*pi/8):=
begin
have : cos(-pi/8) = -sin(5499*pi/8),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (343),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = - sin(11901*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (743),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_513 (h0 : sin(4795*pi/18)≠ 0) : sin(-pi/9)/sin(4795*pi/18)=tan(-pi/9):=
begin
have : cos(-pi/9) = sin(4795*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (133),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) / cos(-pi/9) = tan(-pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_514 : -3*cos(pi/21) + 4*cos(pi/21)**3=- sin(20127*pi/14):=
begin
have : 4 * cos(pi / 21) ** 3 - 3 * cos(pi / 21) = -3*cos(pi/21) + 4*cos(pi/21)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = 4 * cos(pi/21) ** 3 - 3 * cos(pi/21),
{
have : cos(pi/7) = cos(3*(pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = - sin(20127*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (718),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_515 : cos(-2*pi)=-sin(5539*pi/2):=
begin
have : sin(3773*pi/2) = -sin(5539*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3773*pi/2) (441),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(3773*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (944),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_516 : cos(pi/4)**2 + sin(3457*pi/4)**2=1:=
begin
have : sin(3457 * pi / 4) ** 2 + cos(pi / 4) ** 2 = cos(pi/4)**2 + sin(3457*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(3457*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (432),
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


lemma Trigo_number_generalization_step1_517 : -tan(6983*pi/9)=1 / tan(5803*pi/18):=
begin
have : tan(pi/9) = -tan(6983*pi/9),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/9) (776),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 1 / tan(5803*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/9) (322),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_518 (h0 : cos((2*pi/3)/2)≠ 0) (h1 : (cos(2*pi/3)+1)≠ 0) (h2 : (1+cos(2*pi/3))≠ 0) : sin(2*pi/3)/(cos(2*pi/3) + 1)=sqrt( 3 ):=
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
have : tan(pi/3) = sqrt( 3 ),
{
rw tan_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_519 : sin(12021*pi/8) + cos(2*pi)=2 * cos(-17*pi/16) * cos(15*pi/16):=
begin
have : cos(-pi/8) = sin(12021*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/8) (751),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) + cos(2*pi) = 2 * cos(-17*pi/16) * cos(15*pi/16),
{
rw cos_add_cos,
have : cos(((-pi/8) + (2*pi))/2) = cos(15*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/8) - (2*pi))/2) = cos(-17*pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_520 : -sin(pi/6)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/6)=cos(7065*pi/4):=
begin
have : sin(5 * pi / 12) * cos(pi / 6) - sin(pi / 6) * cos(5 * pi / 12) = -sin(pi/6)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(5*pi/12) * cos(pi/6) - sin(pi/6) * cos(5*pi/12),
{
have : sin(pi/4) = sin((5*pi/12) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(7065*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (883),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_521 : -cos(3007*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -cos(3007*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (250),
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


lemma Trigo_number_generalization_step1_522 : -cos(3545*pi/3)=sin(pi/3) * sin(pi) + cos(pi/3) * cos(pi):=
begin
have : cos(-2*pi/3) = -cos(3545*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi/3) (590),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = sin(pi/3) * sin(pi) + cos(pi/3) * cos(pi),
{
have : cos(-2*pi/3) = cos((pi/3) - (pi)),
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


lemma Trigo_number_generalization_step1_523 : cos(63*pi/8)=- cos(9479*pi/8):=
begin
have : cos(-pi/8) = cos(63*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/8) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = - cos(9479*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/8) (592),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_524 : -cos(1405*pi)=sin(521*pi/2):=
begin
have : cos(-2*pi) = -cos(1405*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (701),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(521*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (129),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_525 (h0 : cos((pi/4)/2)≠ 0) (h1 : sin(pi/4)≠ 0) : (1 - cos(pi/4))/sin(pi/4)=tan(1057*pi/8):=
begin
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
have : tan(pi/8) = tan(1057*pi/8),
{
rw tan_eq_tan_add_int_mul_pi (pi/8) (132),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_526 : -4*sin(pi/27)**3 + 3*sin(pi/27)=cos(3715*pi/18):=
begin
have : (-4) * sin(pi / 27) ** 3 + 3 * sin(pi / 27) = -4*sin(pi/27)**3 + 3*sin(pi/27),
{
field_simp at *,
},
have : sin(pi/9) = -4 * sin(pi/27) ** 3 + 3 * sin(pi/27),
{
have : sin(pi/9) = sin(3*(pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = cos(3715*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (103),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_527 : sin(12373*pi/8)=cos(5007*pi/8):=
begin
have : cos(-pi/8) = sin(12373*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/8) (773),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = cos(5007*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/8) (313),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_528 : sin(pi/5) + sin(-pi)=-2*sin(-2*pi/5)*cos(2712*pi/5):=
begin
have : 2 * sin((-2) * pi / 5) * -cos(2712 * pi / 5) = -2*sin(-2*pi/5)*cos(2712*pi/5),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/5) = -cos(2712*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/5) (271),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/5) + sin(-pi) = 2 * sin(-2*pi/5) * cos(3*pi/5),
{
rw sin_add_sin,
have : sin(((pi/5) + (-pi))/2) = sin(-2*pi/5),
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
},
rw this,
end


lemma Trigo_number_generalization_step1_529 : 3*sin(-pi/18) - 4*sin(-pi/18)**3=sin(8099*pi/6):=
begin
have : (-4) * sin(-pi / 18) ** 3 + 3 * sin(-pi / 18) = 3*sin(-pi/18) - 4*sin(-pi/18)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -4 * sin(-pi/18) ** 3 + 3 * sin(-pi/18),
{
have : sin(-pi/6) = sin(3*(-pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(8099*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (675),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_530 : 4*cos(-pi/2)**3 - 3*cos(-pi/2)=- sin(pi/2) * sin(-2*pi) + cos(pi/2) * cos(-2*pi):=
begin
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
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = - sin(pi/2) * sin(-2*pi) + cos(pi/2) * cos(-2*pi),
{
have : cos(-3*pi/2) = cos((pi/2) + (-2*pi)),
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


lemma Trigo_number_generalization_step1_531 : -sin(pi/2)*sin(8416*pi/9)=cos(-7*pi/18) / 2 - cos(11*pi/18) / 2:=
begin
have : -sin(8416 * pi / 9) * sin(pi / 2) = -sin(pi/2)*sin(8416*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = -sin(8416*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/9) (467),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) * sin(pi/2) = cos(-7*pi/18) / 2 - cos(11*pi/18) / 2,
{
rw sin_mul_sin,
have : cos((pi/9) + (pi/2)) = cos(11*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (pi/2)) = cos(-7*pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_532 : -sin(pi/9)*cos(11*pi/18) + sin(11*pi/18)*cos(pi/9)=- sin(3863*pi/2):=
begin
have : sin(11 * pi / 18) * cos(pi / 9) - sin(pi / 9) * cos(11 * pi / 18) = -sin(pi/9)*cos(11*pi/18) + sin(11*pi/18)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(11*pi/18) * cos(pi/9) - sin(pi/9) * cos(11*pi/18),
{
have : sin(pi/2) = sin((11*pi/18) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(3863*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (966),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_533 : -sin(10509*pi/10)=4 * cos(pi/5) ** 3 - 3 * cos(pi/5):=
begin
have : cos(3*pi/5) = -sin(10509*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/5) (525),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/5) = 4 * cos(pi/5) ** 3 - 3 * cos(pi/5),
{
have : cos(3*pi/5) = cos(3*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_534 : sin(9517*pi/6)=1 / 2:=
begin
have : sin(pi/6) = sin(9517*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (793),
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


lemma Trigo_number_generalization_step1_535 : sin(pi/7) ** 2=1 - sin(7387*pi/14)**2:=
begin
have : 1 - (-sin(7387 * pi / 14)) ** 2 = 1 - sin(7387*pi/14)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) = -sin(7387*pi/14),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) ** 2 = 1 - cos(pi/7) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_536 : sin(-pi/2)=-cos(258*pi):=
begin
have : cos(72*pi) = cos(258*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (72*pi) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = - cos(72*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_537 (h0 : cos((pi/3)/2)≠ 0) (h1 : (1+cos(pi/3))≠ 0) (h2 : (cos(pi/3)+1)≠ 0) : sin(pi/6) / cos(pi/6)=sin(pi/3)/(cos(pi/3) + 1):=
begin
have : sin(pi / 3) / (1 + cos(pi / 3)) = sin(pi/3)/(cos(pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi/6) / cos(pi/6) = tan(pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_538 : sin(-pi/9)*sin(22*pi/45) + cos(-pi/9)*cos(22*pi/45)=4 * cos(pi/5) ** 3 - 3 * cos(pi/5):=
begin
have : sin(22 * pi / 45) * sin(-pi / 9) + cos(22 * pi / 45) * cos(-pi / 9) = sin(-pi/9)*sin(22*pi/45) + cos(-pi/9)*cos(22*pi/45),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/5) = sin(22*pi/45) * sin(-pi/9) + cos(22*pi/45) * cos(-pi/9),
{
have : cos(3*pi/5) = cos((22*pi/45) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/5) = 4 * cos(pi/5) ** 3 - 3 * cos(pi/5),
{
have : cos(3*pi/5) = cos(3*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_539 : -sin(26255*pi/14) + cos(pi/9)=2 * cos(-pi/63) * cos(8*pi/63):=
begin
have : cos(pi / 9) + -sin(26255 * pi / 14) = -sin(26255*pi/14) + cos(pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = -sin(26255*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (937),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) + cos(pi/7) = 2 * cos(-pi/63) * cos(8*pi/63),
{
rw cos_add_cos,
have : cos(((pi/9) + (pi/7))/2) = cos(8*pi/63),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/9) - (pi/7))/2) = cos(-pi/63),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_540 : -2*sin(9*pi/10)*cos(11*pi/10)=2 * sin(-9*pi/10) * cos(11*pi/10):=
begin
have : (-1) * (2 * sin(9 * pi / 10) * cos(11 * pi / 10)) = -2*sin(9*pi/10)*cos(11*pi/10),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) - sin(pi/5) = 2 * sin(9*pi/10) * cos(11*pi/10),
{
rw sin_sub_sin,
have : cos(((2*pi) + (pi/5))/2) = cos(11*pi/10),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi) - (pi/5))/2) = sin(9*pi/10),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -1*(sin(2*pi) - sin(pi/5)) = sin(pi/5)-sin(2*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(pi/5) - sin(2*pi) = 2 * sin(-9*pi/10) * cos(11*pi/10),
{
rw sin_sub_sin,
have : cos(((pi/5) + (2*pi))/2) = cos(11*pi/10),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/5) - (2*pi))/2) = sin(-9*pi/10),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_541 (h0 : cos(-pi/3)≠ 0) : (-sin(pi/5)*cos(-2*pi/15) + sin(-2*pi/15)*cos(pi/5))/cos(-pi/3)=tan(-pi/3):=
begin
have : (sin((-2) * pi / 15) * cos(pi / 5) - sin(pi / 5) * cos((-2) * pi / 15)) / cos(-pi / 3) = (-sin(pi/5)*cos(-2*pi/15) + sin(-2*pi/15)*cos(pi/5))/cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-2*pi/15) * cos(pi/5) - sin(pi/5) * cos(-2*pi/15),
{
have : sin(-pi/3) = sin((-2*pi/15) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) / cos(-pi/3) = tan(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_542 : sin(-pi)=-sin(-308*pi):=
begin
have : -sin((-308) * pi) = -sin(-308*pi),
{
field_simp at *,
},
have : cos(889*pi/2) = sin(-308*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (889*pi/2) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(889*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (221),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_543 : cos(4870*pi/9)**2=cos(2*pi/9) / 2 + 1 / 2:=
begin
have : (-cos(4870 * pi / 9)) ** 2 = cos(4870*pi/9)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -cos(4870*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/9) (270),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step1_544 : -sin(1446*pi)=- 4 * sin(-pi/3) ** 3 + 3 * sin(-pi/3):=
begin
have : sin(-pi) = -sin(1446*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (723),
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


lemma Trigo_number_generalization_step1_545 : -cos(6405*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -cos(6405*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (800),
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


lemma Trigo_number_generalization_step1_546 : -sin(109*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -sin(109*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (3*pi/4) (14),
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


lemma Trigo_number_generalization_step1_547 : sin(1767*pi/2)=- 1:=
begin
have : cos(pi) = sin(1767*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (442),
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


lemma Trigo_number_generalization_step1_548 : -tan(64*pi/3)=sin(-pi/3) / cos(-pi/3):=
begin
have : tan(-pi/3) = -tan(64*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = sin(-pi/3) / cos(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_549 : cos(9*pi/8)=cos(-pi)*cos(pi/8) + 2*sin(-pi)*sin(pi/16)*cos(pi/16):=
begin
have : 2 * sin(pi / 16) * cos(pi / 16) * sin(-pi) + cos(pi / 8) * cos(-pi) = cos(-pi)*cos(pi/8) + 2*sin(-pi)*sin(pi/16)*cos(pi/16),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) = 2 * sin(pi/16) * cos(pi/16),
{
have : sin(pi/8) = sin(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(9*pi/8) = sin(pi/8) * sin(-pi) + cos(pi/8) * cos(-pi),
{
have : cos(9*pi/8) = cos((pi/8) - (-pi)),
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


lemma Trigo_number_generalization_step1_550 : sin(-4*pi/45)=sin(-pi/5)*cos(-pi/9) - (1 - 2*sin(-pi/10)**2)*sin(-pi/9):=
begin
have : sin(-pi / 5) * cos(-pi / 9) - sin(-pi / 9) * (1 - 2 * sin(-pi / 10) ** 2) = sin(-pi/5)*cos(-pi/9) - (1 - 2*sin(-pi/10)**2)*sin(-pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-4*pi/45) = sin(-pi/5) * cos(-pi/9) - sin(-pi/9) * cos(-pi/5),
{
have : sin(-4*pi/45) = sin((-pi/5) - (-pi/9)),
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


lemma Trigo_number_generalization_step1_551 (h0 : cos(-pi/6)≠ 0) (h1 : (2*cos(-pi/6))≠ 0) : sin(-pi/3)/(2*cos(-pi/6))=sin(10943*pi/6):=
begin
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
have : sin(-pi/6) = sin(10943*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (912),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_552 : sin(3289*pi/4)=- sin(7623*pi/4):=
begin
have : sin(pi/4) = sin(3289*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (411),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = - sin(7623*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/4) (953),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_553 : -cos(1033*pi)=sin(1701*pi/2):=
begin
have : sin(pi/2) = -cos(1033*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (516),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(1701*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (425),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_554 : -sin(5545*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(5545*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (923),
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


lemma Trigo_number_generalization_step1_555 : -cos(2485*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(2485*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (310),
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


lemma Trigo_number_generalization_step1_556 : sin(-2*pi)=2*(1 - 2*sin(-pi/2)**2)*sin(-pi):=
begin
have : 2 * sin(-pi) * (1 - 2 * sin(-pi / 2) ** 2) = 2*(1 - 2*sin(-pi/2)**2)*sin(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_557 : cos(367*pi/2)=cos(2157*pi/2):=
begin
have : cos(-pi/2) = cos(367*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(2157*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (539),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_558 : -3*cos(-pi/3) + 4*cos(-pi/3)**3=sin(1595*pi/2):=
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
have : cos(-pi) = sin(1595*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_559 : -tan(1483*pi/4)=1:=
begin
have : tan(pi/4) = -tan(1483*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (371),
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


lemma Trigo_number_generalization_step1_560 (h0 : tan(1432*pi/3)≠ 0) : 1/tan(1432*pi/3)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = 1 / tan(1432*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (477),
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


lemma Trigo_number_generalization_step1_561 : -sin(2539*pi/2)=cos(1002*pi):=
begin
have : cos(2*pi) = -sin(2539*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (635),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(1002*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (500),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_562 : 2*sin(-pi/16)*cos(-pi/16)=- cos(4733*pi/8):=
begin
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
have : sin(-pi/8) = - cos(4733*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (295),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_563 : sin(5191*pi/8)=- sin(pi/4) * sin(pi/8) + cos(pi/4) * cos(pi/8):=
begin
have : cos(3*pi/8) = sin(5191*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/8) (324),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = - sin(pi/4) * sin(pi/8) + cos(pi/4) * cos(pi/8),
{
have : cos(3*pi/8) = cos((pi/4) + (pi/8)),
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


lemma Trigo_number_generalization_step1_564 : -cos(463*pi)=1:=
begin
have : sin(pi/2) = -cos(463*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (231),
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


lemma Trigo_number_generalization_step1_565 : (sin(-pi/7)*cos(2*pi/7) + sin(2*pi/7)*cos(-pi/7))*cos(-pi/7)=sin(2*pi/7) / 2 + sin(0) / 2:=
begin
have : (sin(2 * pi / 7) * cos(-pi / 7) + sin(-pi / 7) * cos(2 * pi / 7)) * cos(-pi / 7) = (sin(-pi/7)*cos(2*pi/7) + sin(2*pi/7)*cos(-pi/7))*cos(-pi/7),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(2*pi/7) * cos(-pi/7) + sin(-pi/7) * cos(2*pi/7),
{
have : sin(pi/7) = sin((2*pi/7) + (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) * cos(-pi/7) = sin(2*pi/7) / 2 + sin(0) / 2,
{
rw sin_mul_cos,
have : sin((pi/7) + (-pi/7)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/7) - (-pi/7)) = sin(2*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_566 : -4*sin(pi/4)**3 + 3*sin(pi/4)=sqrt( 2 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_567 : sin(-13*pi/42)/2 - sin(pi/42)/2=sin(-pi/42) / 2 + sin(-13*pi/42) / 2:=
begin
have : -sin(pi / 42) / 2 + sin((-13) * pi / 42) / 2 = sin(-13*pi/42)/2 - sin(pi/42)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(-pi/7) = -sin(pi/42) / 2 + sin(-13*pi/42) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/7) + (-pi/6)) = sin(-13*pi/42),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/7) - (-pi/6)) = sin(pi/42),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi/6) * cos(-pi/7)) = sin(-pi/6)*cos(-pi/7),
{
ring,
},
have : sin(-pi/6) * cos(-pi/7) = sin(-pi/42) / 2 + sin(-13*pi/42) / 2,
{
rw sin_mul_cos,
have : sin((-pi/6) + (-pi/7)) = sin(-13*pi/42),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (-pi/7)) = sin(-pi/42),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_568 : -sin(11485*pi/6) + sin(-pi)=2 * sin(-7*pi/12) * cos(-5*pi/12):=
begin
have : sin(-pi) - sin(11485 * pi / 6) = -sin(11485*pi/6) + sin(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(11485*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (957),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) - sin(pi/6) = 2 * sin(-7*pi/12) * cos(-5*pi/12),
{
rw sin_sub_sin,
have : cos(((-pi) + (pi/6))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (pi/6))/2) = sin(-7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_569 : sin(257*pi/2)**2=1 - sin(pi) ** 2:=
begin
have : (-sin(257 * pi / 2)) ** 2 = sin(257*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(257*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (63),
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


lemma Trigo_number_generalization_step1_570 (h0 : tan(1787*pi/3)≠ 0) : -1/tan(1787*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(1787 * pi / 3) = -1/tan(1787*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1787*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (595),
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


lemma Trigo_number_generalization_step1_571 : -cos(5157*pi/4)=1 - 2 * sin(-pi/8) ** 2:=
begin
have : cos(-pi/4) = -cos(5157*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (644),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_number_generalization_step1_572 (h0 : cos(7*pi/4)≠ 0) (h1 : cos(pi)≠ 0) (h2 : (tan(pi)*tan(7*pi/4)+1)≠ 0) (h3 : (1+tan(7*pi/4)*tan(pi))≠ 0) : (tan(7*pi/4) - tan(pi))/(tan(pi)*tan(7*pi/4) + 1)=- 1:=
begin
have : (tan(7 * pi / 4) - tan(pi)) / (1 + tan(7 * pi / 4) * tan(pi)) = (tan(7*pi/4) - tan(pi))/(tan(pi)*tan(7*pi/4) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = ( tan(7*pi/4) - tan(pi) ) / ( 1 + tan(7*pi/4) * tan(pi) ),
{
have : tan(3*pi/4) = tan((7*pi/4) - (pi)),
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


lemma Trigo_number_generalization_step1_573 : -tan(2378*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(2378*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (793),
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


lemma Trigo_number_generalization_step1_574 : cos(pi/5)*cos(1652*pi/3)=- sin(11*pi/30) / 2 + sin(pi/30) / 2:=
begin
have : cos(1652 * pi / 3) * cos(pi / 5) = cos(pi/5)*cos(1652*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(1652*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (275),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(pi/5) = - sin(11*pi/30) / 2 + sin(pi/30) / 2,
{
rw mul_comm,
rw cos_mul_sin,
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_575 : -sin(pi/8)**2 + cos(pi/8)**2=- cos(4517*pi/4):=
begin
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
have : cos(pi/4) = - cos(4517*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (564),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_576 : sin(-15*pi/56)*cos(-pi/7) + sin(-pi) - sin(-pi/7)*cos(-15*pi/56)=2 * sin(-9*pi/16) * cos(-7*pi/16):=
begin
have : sin(-pi) + (sin((-15) * pi / 56) * cos(-pi / 7) - sin(-pi / 7) * cos((-15) * pi / 56)) = sin(-15*pi/56)*cos(-pi/7) + sin(-pi) - sin(-pi/7)*cos(-15*pi/56),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(-15*pi/56) * cos(-pi/7) - sin(-pi/7) * cos(-15*pi/56),
{
have : sin(-pi/8) = sin((-15*pi/56) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) + sin(-pi/8) = 2 * sin(-9*pi/16) * cos(-7*pi/16),
{
rw sin_add_sin,
have : sin(((-pi) + (-pi/8))/2) = sin(-9*pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (-pi/8))/2) = cos(-7*pi/16),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_577 : sin(-3*pi/2)*sin(-pi/2) + cos(-3*pi/2)*cos(-pi/2)=4 * cos(-pi/3) ** 3 - 3 * cos(-pi/3):=
begin
have : sin((-3) * pi / 2) * sin(-pi / 2) + cos((-3) * pi / 2) * cos(-pi / 2) = sin(-3*pi/2)*sin(-pi/2) + cos(-3*pi/2)*cos(-pi/2),
{
field_simp at *,
},
have : cos(-pi) = sin(-3*pi/2) * sin(-pi/2) + cos(-3*pi/2) * cos(-pi/2),
{
have : cos(-pi) = cos((-3*pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_number_generalization_step1_578 : sin(178*pi/5)=2 * sin(-pi/5) * cos(-pi/5):=
begin
have : sin(-2*pi/5) = sin(178*pi/5),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi/5) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_579 : cos(pi/6)=-sin(3869*pi/3):=
begin
have : sin(3236*pi/3) = -sin(3869*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (3236*pi/3) (105),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(3236*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (539),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_580 (h0 : cos(-pi/6)≠ 0) : cos(2458*pi/3)/cos(-pi/6)=tan(-pi/6):=
begin
have : sin(-pi/6) = cos(2458*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (409),
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


lemma Trigo_number_generalization_step1_581 (h0 : cos(pi/9)≠ 0) : -cos(16225*pi/18)/cos(pi/9)=tan(pi/9):=
begin
have : sin(pi/9) = -cos(16225*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (450),
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


lemma Trigo_number_generalization_step1_582 : -cos(2219*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -cos(2219*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (277),
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


lemma Trigo_number_generalization_step1_583 : (-sin(-2*pi/35)*sin(pi/5) + cos(-2*pi/35)*cos(pi/5))**2=cos(2*pi/7) / 2 + 1 / 2:=
begin
have : (-sin((-2) * pi / 35) * sin(pi / 5) + cos((-2) * pi / 35) * cos(pi / 5)) ** 2 = (-sin(-2*pi/35)*sin(pi/5) + cos(-2*pi/35)*cos(pi/5))**2,
{
field_simp at *,
},
have : cos(pi/7) = -sin(-2*pi/35) * sin(pi/5) + cos(-2*pi/35) * cos(pi/5),
{
have : cos(pi/7) = cos((-2*pi/35) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) ** 2 = cos(2*pi/7) / 2 + 1 / 2,
{
have : cos(2*pi/7) = cos(2*(pi/7)),
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


lemma Trigo_number_generalization_step1_584 : -sin(1579*pi/2)=4 * cos(-2*pi) ** 3 - 3 * cos(-2*pi):=
begin
have : cos(-6*pi) = -sin(1579*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-6*pi) (391),
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


lemma Trigo_number_generalization_step1_585 : -cos(11603*pi/18)=- sin(14320*pi/9):=
begin
have : sin(pi/9) = -cos(11603*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/9) (322),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = - sin(14320*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/9) (795),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_586 : cos(pi/7) + sin(10405*pi/8)=2 * cos(-15*pi/112) * cos(pi/112):=
begin
have : sin(10405 * pi / 8) + cos(pi / 7) = cos(pi/7) + sin(10405*pi/8),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = sin(10405*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/8) (650),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) + cos(pi/7) = 2 * cos(-15*pi/112) * cos(pi/112),
{
rw cos_add_cos,
have : cos(((-pi/8) + (pi/7))/2) = cos(pi/112),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/8) - (pi/7))/2) = cos(-15*pi/112),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_587 (h0 : (-3*cos(-pi/21)+4*cos(-pi/21)**3)≠ 0) (h1 : (4*cos(-pi/21)**3-3*cos(-pi/21))≠ 0) : tan(-pi/7)=sin(-pi/7)/(-3*cos(-pi/21) + 4*cos(-pi/21)**3):=
begin
have : sin(-pi / 7) / (4 * cos(-pi / 21) ** 3 - 3 * cos(-pi / 21)) = sin(-pi/7)/(-3*cos(-pi/21) + 4*cos(-pi/21)**3),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/7) = 4 * cos(-pi/21) ** 3 - 3 * cos(-pi/21),
{
have : cos(-pi/7) = cos(3*(-pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/7) = sin(-pi/7) / cos(-pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_588 (h0 : cos(pi/7)≠ 0) (h1 : (4*cos(pi/7)**2)≠ 0) (h2 : (2*cos(pi/7))≠ 0) : cos(2*pi/7)=-sin(2*pi/7)**2/(4*cos(pi/7)**2) + cos(pi/7)**2:=
begin
have : -(sin(2 * pi / 7) / (2 * cos(pi / 7))) ** 2 + cos(pi / 7) ** 2 = -sin(2*pi/7)**2/(4*cos(pi/7)**2) + cos(pi/7)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_589 : -sin(4833*pi/4)=sin(7365*pi/4):=
begin
have : sin(-pi/4) = -sin(4833*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (604),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(7365*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/4) (920),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_590 : sin(-pi/4) + sin(-2*pi)=sin(-pi/4) - sin(2*pi):=
begin
have : 2 * (-sin(2 * pi) / 2 + sin(-pi / 4) / 2) = sin(-pi/4) - sin(2*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-9*pi/8) * cos(7*pi/8) = -sin(2*pi) / 2 + sin(-pi/4) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((7*pi/8) + (-9*pi/8)) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((7*pi/8) - (-9*pi/8)) = sin(2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-9*pi/8) * cos(7*pi/8)) = 2*sin(-9*pi/8)*cos(7*pi/8),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi/4) + sin(-2*pi) = 2 * sin(-9*pi/8) * cos(7*pi/8),
{
rw sin_add_sin,
have : sin(((-pi/4) + (-2*pi))/2) = sin(-9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/4) - (-2*pi))/2) = cos(7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_591 : -3*cos(-pi/6) + 4*cos(-pi/6)**3=1 - 2 * sin(-pi/4) ** 2:=
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


lemma Trigo_number_generalization_step1_592 (h0 : cos(-pi/8)≠ 0) : (3*sin(-pi/24) - 4*sin(-pi/24)**3)/cos(-pi/8)=tan(-pi/8):=
begin
have : ((-4) * sin(-pi / 24) ** 3 + 3 * sin(-pi / 24)) / cos(-pi / 8) = (3*sin(-pi/24) - 4*sin(-pi/24)**3)/cos(-pi/8),
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
have : sin(-pi/8) / cos(-pi/8) = tan(-pi/8),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_593 : -sin(5837*pi/6)=sin(79*pi/6):=
begin
have : sin(-pi/6) = -sin(5837*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (486),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(79*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_594 : sin(-pi/4) - sin(1952*pi)=2 * sin(-9*pi/8) * cos(7*pi/8):=
begin
have : sin(2*pi) = sin(1952*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (975),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) - sin(2*pi) = 2 * sin(-9*pi/8) * cos(7*pi/8),
{
rw sin_sub_sin,
have : cos(((-pi/4) + (2*pi))/2) = cos(7*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/4) - (2*pi))/2) = sin(-9*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_595 : -sin(956*pi)=- sin(902*pi):=
begin
have : sin(2*pi) = -sin(956*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (479),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(902*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (452),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_596 : -cos(901*pi)=- cos(1765*pi):=
begin
have : sin(pi/2) = -cos(901*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (450),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - cos(1765*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (882),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_597 : -cos(5323*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -cos(5323*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (665),
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


lemma Trigo_number_generalization_step1_598 : sin(pi/4)=2*(-1 + 2*cos(pi/16)**2)*sin(pi/8):=
begin
have : 2 * sin(pi / 8) * (2 * cos(pi / 16) ** 2 - 1) = 2*(-1 + 2*cos(pi/16)**2)*sin(pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_599 : -tan(678*pi)=0:=
begin
have : tan(pi) = -tan(678*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (679),
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


lemma Trigo_number_generalization_step1_600 : cos(5545*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = cos(5545*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (462),
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


lemma Trigo_number_generalization_step1_601 : (sin(-12*pi/35)*cos(pi/5) + sin(pi/5)*cos(-12*pi/35))**2=1 / 2 - cos(-2*pi/7) / 2:=
begin
have : (sin((-12) * pi / 35) * cos(pi / 5) + sin(pi / 5) * cos((-12) * pi / 35)) ** 2 = (sin(-12*pi/35)*cos(pi/5) + sin(pi/5)*cos(-12*pi/35))**2,
{
field_simp at *,
},
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
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_602 (h0 : cos((2*pi/9)/2)≠ 0) (h1 : (cos(2*pi/9)+1)≠ 0) (h2 : (1+cos(2*pi/9))≠ 0) : sin(2*pi/9)/(cos(2*pi/9) + 1)=- 1 / tan(10289*pi/18):=
begin
have : sin(2 * pi / 9) / (1 + cos(2 * pi / 9)) = sin(2*pi/9)/(cos(2*pi/9) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = sin(2*pi/9) / ( 1 + cos(2*pi/9) ),
{
have : tan(pi/9) = tan((2*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = - 1 / tan(10289*pi/18),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/9) (571),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_603 : -cos(2605*pi/2)=0:=
begin
have : sin(pi) = -cos(2605*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (651),
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


lemma Trigo_number_generalization_step1_604 : -sin(3*pi/8)**2 + cos(3*pi/8)**2=- sqrt( 2 ) / 2:=
begin
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


lemma Trigo_number_generalization_step1_605 (h0 : cos(-pi/30)≠ 0) (h1 : cos(pi/6)≠ 0) (h2 : (1+tan(-pi/30)*tan(pi/6))≠ 0) (h3 : (tan(-pi/30)*tan(pi/6)+1)≠ 0) : (-tan(pi/6) + tan(-pi/30))/(tan(-pi/30)*tan(pi/6) + 1)=tan(2744*pi/5):=
begin
have : (tan(-pi / 30) - tan(pi / 6)) / (1 + tan(-pi / 30) * tan(pi / 6)) = (-tan(pi/6) + tan(-pi/30))/(tan(-pi/30)*tan(pi/6) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = ( tan(-pi/30) - tan(pi/6) ) / ( 1 + tan(-pi/30) * tan(pi/6) ),
{
have : tan(-pi/5) = tan((-pi/30) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/5) = tan(2744*pi/5),
{
rw tan_eq_tan_add_int_mul_pi (-pi/5) (549),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_606 : -sin(6215*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -sin(6215*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/4) (777),
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


lemma Trigo_number_generalization_step1_607 : 1 - 2*sin(pi/16)**2=sin(11941*pi/8):=
begin
have : cos(pi/8) = 1 - 2 * sin(pi/16) ** 2,
{
have : cos(pi/8) = cos(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = sin(11941*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/8) (746),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_608 : -sin(345*pi)=0:=
begin
have : sin(pi) = -sin(345*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (173),
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


lemma Trigo_number_generalization_step1_609 : cos(-pi)=1 - 2*(3*sin(-pi/6) - 4*sin(-pi/6)**3)**2:=
begin
have : 1 - 2 * ((-4) * sin(-pi / 6) ** 3 + 3 * sin(-pi / 6)) ** 2 = 1 - 2*(3*sin(-pi/6) - 4*sin(-pi/6)**3)**2,
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


lemma Trigo_number_generalization_step1_610 : sin(pi/7)=sin(pi/6)*sin(3553*pi/21) - cos(pi/6)*cos(3553*pi/21):=
begin
have : -(-sin(3553 * pi / 21) * sin(pi / 6) + cos(3553 * pi / 21) * cos(pi / 6)) = sin(pi/6)*sin(3553*pi/21) - cos(pi/6)*cos(3553*pi/21),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2371*pi/14) = -sin(3553*pi/21) * sin(pi/6) + cos(3553*pi/21) * cos(pi/6),
{
have : cos(2371*pi/14) = cos((3553*pi/21) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) = - cos(2371*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_611 : sin(-pi/2)*sin(pi/6) + cos(-pi/2)*cos(pi/6)=- 1 / 2:=
begin
have : sin(pi / 6) * sin(-pi / 2) + cos(pi / 6) * cos(-pi / 2) = sin(-pi/2)*sin(pi/6) + cos(-pi/2)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(pi/6) * sin(-pi/2) + cos(pi/6) * cos(-pi/2),
{
have : cos(2*pi/3) = cos((pi/6) - (-pi/2)),
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


lemma Trigo_number_generalization_step1_612 : sin(-pi/3) - sin(275*pi)=2 * sin(5*pi/6) * cos(-7*pi/6):=
begin
have : sin(-pi / 3) + -sin(275 * pi) = sin(-pi/3) - sin(275*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(275*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (136),
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


lemma Trigo_number_generalization_step1_613 : sin(pi/6)=cos(-pi/6)*cos(939*pi/2) + sin(-pi/6)*sin(939*pi/2):=
begin
have : sin(939 * pi / 2) * sin(-pi / 6) + cos(939 * pi / 2) * cos(-pi / 6) = cos(-pi/6)*cos(939*pi/2) + sin(-pi/6)*sin(939*pi/2),
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(1409*pi/3) = sin(939*pi/2) * sin(-pi/6) + cos(939*pi/2) * cos(-pi/6),
{
have : cos(1409*pi/3) = cos((939*pi/2) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = cos(1409*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (234),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_614 : sin(6619*pi/4)=- cos(4219*pi/4):=
begin
have : cos(-pi/4) = sin(6619*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (827),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - cos(4219*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/4) (527),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_615 : 4*sin(pi/4)**2*cos(pi/4)**2=1 / 2 - cos(pi) / 2:=
begin
have : (sin(pi / 4) * cos(pi / 4) + sin(pi / 4) * cos(pi / 4)) ** 2 = 4*sin(pi/4)**2*cos(pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(pi/4) * cos(pi/4) + sin(pi/4) * cos(pi/4),
{
have : sin(pi/2) = sin((pi/4) + (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step1_616 : -tan(3947*pi/4)=1:=
begin
have : tan(pi/4) = -tan(3947*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (987),
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


lemma Trigo_number_generalization_step1_617 : 2*sin(-5*pi/9)*cos(-5*pi/9)=sin(-pi) * cos(pi/9) - sin(pi/9) * cos(-pi):=
begin
have : 2 * sin((-5) * pi / 9) * cos((-5) * pi / 9) = 2*sin(-5*pi/9)*cos(-5*pi/9),
{
field_simp at *,
},
have : sin(-10*pi/9) = 2 * sin(-5*pi/9) * cos(-5*pi/9),
{
have : sin(-10*pi/9) = sin(2*(-5*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-10*pi/9) = sin(-pi) * cos(pi/9) - sin(pi/9) * cos(-pi),
{
have : sin(-10*pi/9) = sin((-pi) - (pi/9)),
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


lemma Trigo_number_generalization_step1_618 : -sin(pi/12)**2 + cos(pi/12)**2 + cos(-2*pi)=2 * cos(-13*pi/12) * cos(-11*pi/12):=
begin
have : cos((-2) * pi) + (-sin(pi / 12) ** 2 + cos(pi / 12) ** 2) = -sin(pi/12)**2 + cos(pi/12)**2 + cos(-2*pi),
{
field_simp at *,
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


lemma Trigo_number_generalization_step1_619 : sin(-pi/3)*cos(11195*pi/6)=- sin(pi/2) / 2 + sin(-pi/6) / 2:=
begin
have : cos(pi/6) = cos(11195*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (933),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi/6) = - sin(pi/2) / 2 + sin(-pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_620 : sin(-2*pi)*cos(9*pi/4) + sin(9*pi/4)*cos(-2*pi)=sqrt( 2 ) / 2:=
begin
have : sin(9 * pi / 4) * cos((-2) * pi) + sin((-2) * pi) * cos(9 * pi / 4) = sin(-2*pi)*cos(9*pi/4) + sin(9*pi/4)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(9*pi/4) * cos(-2*pi) + sin(-2*pi) * cos(9*pi/4),
{
have : sin(pi/4) = sin((9*pi/4) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_621 : cos(341*pi/2)=- cos(2345*pi/2):=
begin
have : cos(pi/2) = cos(341*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(2345*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (586),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_622 : -sin(7493*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -sin(7493*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (936),
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


lemma Trigo_number_generalization_step1_623 : -tan(2085*pi/4)=- 1:=
begin
have : tan(3*pi/4) = -tan(2085*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (522),
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


lemma Trigo_number_generalization_step1_624 : sin(19*pi)=2 * sin(pi/2) * cos(pi/2):=
begin
have : sin(pi) = sin(19*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (9),
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
rw this,
end


lemma Trigo_number_generalization_step1_625 : (-sin(pi/18)**2 + cos(pi/18)**2)*cos(-pi/6)=cos(5*pi/18) / 2 + cos(-pi/18) / 2:=
begin
have : cos(pi/9) = -sin(pi/18) ** 2 + cos(pi/18) ** 2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) * cos(-pi/6) = cos(5*pi/18) / 2 + cos(-pi/18) / 2,
{
rw cos_mul_cos,
have : cos((pi/9) + (-pi/6)) = cos(-pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (-pi/6)) = cos(5*pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_626 : -cos(1623*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -cos(1623*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (3*pi/4) (202),
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


lemma Trigo_number_generalization_step1_627 : sin(pi)=1 - 2*sin(2107*pi/4)**2:=
begin
have : cos(2107*pi/2) = 1 - 2 * sin(2107*pi/4) ** 2,
{
have : cos(2107*pi/2) = cos(2*(2107*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi) = cos(2107*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (527),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_628 : sin(6993*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = sin(6993*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (874),
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


lemma Trigo_number_generalization_step1_629 : -cos(4364*pi/3)=1 / 2:=
begin
have : cos(pi/3) = -cos(4364*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (727),
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


lemma Trigo_number_generalization_step1_630 : sin(10697*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = sin(10697*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi/6) (891),
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


lemma Trigo_number_generalization_step1_631 : (-sin(-pi/3)*sin(pi/12) + cos(-pi/3)*cos(pi/12))**2=1 - sin(-pi/4) ** 2:=
begin
have : (-sin(pi / 12) * sin(-pi / 3) + cos(pi / 12) * cos(-pi / 3)) ** 2 = (-sin(-pi/3)*sin(pi/12) + cos(-pi/3)*cos(pi/12))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -sin(pi/12) * sin(-pi/3) + cos(pi/12) * cos(-pi/3),
{
have : cos(-pi/4) = cos((pi/12) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) ** 2 = 1 - sin(-pi/4) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_632 : cos(7249*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = cos(7249*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (905),
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


lemma Trigo_number_generalization_step1_633 (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : sin(pi/3)/(2*sin(pi/6))=sqrt( 3 ) / 2:=
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_634 : cos(pi/8) - cos(8920*pi/9)=2 * cos(-17*pi/144) * cos(pi/144):=
begin
have : -cos(8920 * pi / 9) + cos(pi / 8) = cos(pi/8) - cos(8920*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = -cos(8920*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/9) (495),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) + cos(pi/8) = 2 * cos(-17*pi/144) * cos(pi/144),
{
rw cos_add_cos,
have : cos(((-pi/9) + (pi/8))/2) = cos(pi/144),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (pi/8))/2) = cos(-17*pi/144),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_635 : 1 - 2*sin(5*pi/12)**2=- sqrt( 3 ) / 2:=
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
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_636 : cos(-pi/8)=sin(26449*pi/24)*cos(-pi/3) - sin(-pi/3)*cos(26449*pi/24):=
begin
have : sin(8819*pi/8) = sin(26449*pi/24) * cos(-pi/3) - sin(-pi/3) * cos(26449*pi/24),
{
have : sin(8819*pi/8) = sin((26449*pi/24) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = sin(8819*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/8) (551),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_637 : tan(215*pi)=0:=
begin
have : tan(pi) = tan(215*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (214),
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


lemma Trigo_number_generalization_step1_638 : -sin(2843*pi/5)=2 * sin(-pi/5) * cos(-pi/5):=
begin
have : sin(-2*pi/5) = -sin(2843*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/5) (284),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_639 : sin(-pi/8)*cos(-pi/4) - sin(-pi/4)*cos(-pi/8)=- sin(6895*pi/8):=
begin
have : sin(pi/8) = sin(-pi/8) * cos(-pi/4) - sin(-pi/4) * cos(-pi/8),
{
have : sin(pi/8) = sin((-pi/8) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = - sin(6895*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/8) (431),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_640 : -cos(pi/6)*cos(13*pi/42) - sin(pi/6)*sin(13*pi/42) + cos(pi/4)=- 2 * sin(3*pi/56) * sin(11*pi/56):=
begin
have : cos(pi / 4) - (sin(13 * pi / 42) * sin(pi / 6) + cos(13 * pi / 42) * cos(pi / 6)) = -cos(pi/6)*cos(13*pi/42) - sin(pi/6)*sin(13*pi/42) + cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = sin(13*pi/42) * sin(pi/6) + cos(13*pi/42) * cos(pi/6),
{
have : cos(pi/7) = cos((13*pi/42) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) - cos(pi/7) = - 2 * sin(3*pi/56) * sin(11*pi/56),
{
rw cos_sub_cos,
have : sin(((pi/4) + (pi/7))/2) = sin(11*pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/4) - (pi/7))/2) = sin(3*pi/56),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_641 : sin(-pi/3)=-sin(pi/2)*cos(pi/6) + (1 - 2*sin(pi/4)**2)*sin(pi/6):=
begin
have : sin(pi / 6) * (1 - 2 * sin(pi / 4) ** 2) - sin(pi / 2) * cos(pi / 6) = -sin(pi/2)*cos(pi/6) + (1 - 2*sin(pi/4)**2)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
rw ← this,
end


lemma Trigo_number_generalization_step1_642 : -tan(5776*pi/7)=1 / tan(9459*pi/14):=
begin
have : tan(-pi/7) = -tan(5776*pi/7),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/7) (825),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/7) = 1 / tan(9459*pi/14),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/7) (675),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_643 (h0 : tan(3373*pi/6)≠ 0) : -1/tan(3373*pi/6)=- sqrt( 3 ):=
begin
have : (-1) / tan(3373 * pi / 6) = -1/tan(3373*pi/6),
{
field_simp at *,
},
have : tan(2*pi/3) = -1 / tan(3373*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi/3) (561),
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


lemma Trigo_number_generalization_step1_644 (h0 : cos(pi/9)≠ 0) : tan(pi/9)=cos(12593*pi/18)/cos(pi/9):=
begin
have : sin(pi/9) = cos(12593*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (349),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/9) = sin(pi/9) / cos(pi/9),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_645 : cos(789*pi/2)=cos(495*pi/2):=
begin
have : sin(-pi) = cos(789*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (197),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(495*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (123),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_646 : -sin(1990*pi)=0:=
begin
have : cos(pi/2) = -sin(1990*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (994),
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


lemma Trigo_number_generalization_step1_647 : (-sin(pi/9)*cos(-pi/72) + sin(-pi/72)*cos(pi/9))**2=1 - cos(-pi/8) ** 2:=
begin
have : (sin(-pi / 72) * cos(pi / 9) - sin(pi / 9) * cos(-pi / 72)) ** 2 = (-sin(pi/9)*cos(-pi/72) + sin(-pi/72)*cos(pi/9))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = sin(-pi/72) * cos(pi/9) - sin(pi/9) * cos(-pi/72),
{
have : sin(-pi/8) = sin((-pi/72) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) ** 2 = 1 - cos(-pi/8) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_648 : -cos(1551*pi/2)=- sin(181*pi):=
begin
have : cos(pi/2) = -cos(1551*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (387),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - sin(181*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_649 : -cos(3645*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(3645*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (455),
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


lemma Trigo_number_generalization_step1_650 : -cos(23533*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(23533*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (980),
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


lemma Trigo_number_generalization_step1_651 : -cos(5681*pi/6)=- sin(658*pi/3):=
begin
have : sin(pi/3) = -cos(5681*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (473),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(658*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (109),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_652 : -sin(-pi/5)*cos(-6*pi/5) + sin(-6*pi/5)*cos(-pi/5)=cos(3377*pi/2):=
begin
have : sin((-6) * pi / 5) * cos(-pi / 5) - sin(-pi / 5) * cos((-6) * pi / 5) = -sin(-pi/5)*cos(-6*pi/5) + sin(-6*pi/5)*cos(-pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(-6*pi/5) * cos(-pi/5) - sin(-pi/5) * cos(-6*pi/5),
{
have : sin(-pi) = sin((-6*pi/5) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(3377*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (844),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_653 : 1 - 2*sin(pi)**2=- cos(1905*pi):=
begin
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
have : cos(2*pi) = - cos(1905*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (951),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_654 : sin(-2*pi/3)=2*(-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(-pi/3):=
begin
have : 2 * sin(-pi / 3) * (-sin(-pi / 6) ** 2 + cos(-pi / 6) ** 2) = 2*(-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(-pi/3),
{
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-2*pi/3) = 2 * sin(-pi/3) * cos(-pi/3),
{
have : sin(-2*pi/3) = sin(2*(-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_655 : 2*sin(-pi)*cos(-pi)=- cos(87*pi/2):=
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
have : sin(-2*pi) = - cos(87*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_656 : cos(10901*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = cos(10901*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (5*pi/6) (908),
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


lemma Trigo_number_generalization_step1_657 : cos(-59*pi/24)*cos(pi/3) - sin(-59*pi/24)*sin(pi/3)=sin(-pi/8) * sin(2*pi) + cos(-pi/8) * cos(2*pi):=
begin
have : -sin((-59) * pi / 24) * sin(pi / 3) + cos((-59) * pi / 24) * cos(pi / 3) = cos(-59*pi/24)*cos(pi/3) - sin(-59*pi/24)*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-17*pi/8) = -sin(-59*pi/24) * sin(pi/3) + cos(-59*pi/24) * cos(pi/3),
{
have : cos(-17*pi/8) = cos((-59*pi/24) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-17*pi/8) = sin(-pi/8) * sin(2*pi) + cos(-pi/8) * cos(2*pi),
{
have : cos(-17*pi/8) = cos((-pi/8) - (2*pi)),
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


lemma Trigo_number_generalization_step1_658 : sin(2503*pi/2)=- 1:=
begin
have : cos(pi) = sin(2503*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (626),
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


lemma Trigo_number_generalization_step1_659 : -sin(5153*pi/3)=cos(11807*pi/6):=
begin
have : sin(pi/3) = -sin(5153*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (859),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(11807*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (983),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_660 : (sin(-pi/2)*sin(pi/2) + cos(-pi/2)*cos(pi/2))**2=cos(-2*pi) / 2 + 1 / 2:=
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


lemma Trigo_number_generalization_step1_661 : cos(pi/7) - cos(-2*pi)=-2*(sin(59*pi/42)*cos(pi/3) - sin(pi/3)*cos(59*pi/42))*sin(-13*pi/14):=
begin
have : (-2) * (sin(59 * pi / 42) * cos(pi / 3) - sin(pi / 3) * cos(59 * pi / 42)) * sin((-13) * pi / 14) = -2*(sin(59*pi/42)*cos(pi/3) - sin(pi/3)*cos(59*pi/42))*sin(-13*pi/14),
{
field_simp at *,
},
have : sin(15*pi/14) = sin(59*pi/42) * cos(pi/3) - sin(pi/3) * cos(59*pi/42),
{
have : sin(15*pi/14) = sin((59*pi/42) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) - cos(-2*pi) = - 2 * sin(15*pi/14) * sin(-13*pi/14),
{
rw cos_sub_cos,
have : sin(((pi/7) + (-2*pi))/2) = sin(-13*pi/14),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/7) - (-2*pi))/2) = sin(15*pi/14),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_662 : -cos(1741*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = -cos(1741*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (290),
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


lemma Trigo_number_generalization_step1_663 (h0 : tan(5275*pi/6)≠ 0) : 1/tan(5275*pi/6)=sqrt( 3 ):=
begin
have : tan(pi/3) = 1 / tan(5275*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (879),
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


lemma Trigo_number_generalization_step1_664 : -tan(693*pi)=0:=
begin
have : tan(pi) = -tan(693*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (694),
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


lemma Trigo_number_generalization_step1_665 : -1 + 2*cos(pi)**2=1 - 2 * sin(pi) ** 2:=
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


lemma Trigo_number_generalization_step1_666 : -4*sin(pi/18)**3 + 3*sin(pi/18)=1 / 2:=
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
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_667 : sin(8761*pi/6)=- cos(4328*pi/3):=
begin
have : cos(-pi/3) = sin(8761*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (730),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(4328*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (721),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_668 (h0 : cos(pi/6)≠ 0) : sin(pi/6)/cos(pi/6)=sqrt( 3 ) / 3:=
begin
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


lemma Trigo_number_generalization_step1_669 (h0 : cos(pi/24)≠ 0) (h1 : (1-tan(pi/24)**2)≠ 0) : 2*tan(pi/24)/(1 - tan(pi/24)**2)=2 - sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_670 (h0 : tan(916*pi)≠ 0) : -1/tan(916*pi)=tan(583*pi/2):=
begin
have : (-1) / tan(916 * pi) = -1/tan(916*pi),
{
field_simp at *,
},
have : tan(pi/2) = -1 / tan(916*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (915),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = tan(583*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (291),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_671 (h0 : tan(1129*pi/2)≠ 0) : -1/tan(1129*pi/2)=tan(611*pi):=
begin
have : (-1) / tan(1129 * pi / 2) = -1/tan(1129*pi/2),
{
field_simp at *,
},
have : tan(pi) = -1 / tan(1129*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (563),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = tan(611*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (610),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_672 : -cos(4107*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = -cos(4107*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (513),
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


lemma Trigo_number_generalization_step1_673 : -cos(126*pi)=4 * cos(pi/3) ** 3 - 3 * cos(pi/3):=
begin
have : cos(pi) = -cos(126*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (63),
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


lemma Trigo_number_generalization_step1_674 : sin(6917*pi/6)=1 / 2:=
begin
have : sin(pi/6) = sin(6917*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (576),
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


lemma Trigo_number_generalization_step1_675 (h0 : sin(6*pi)≠ 0) (h1 : (2*sin(6*pi))≠ 0) : sin(12*pi)/(2*sin(6*pi))=4 * cos(2*pi) ** 3 - 3 * cos(2*pi):=
begin
have : cos(6*pi) = sin(12*pi) / ( 2 * sin(6*pi) ),
{
have : sin(12*pi) = sin(2*(6*pi)),
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


lemma Trigo_number_generalization_step1_676 : sin(15*pi/56)=(-1 + 2*cos(pi/14)**2)*sin(pi/8) + sin(pi/7)*cos(pi/8):=
begin
have : sin(pi / 7) * cos(pi / 8) + sin(pi / 8) * (2 * cos(pi / 14) ** 2 - 1) = (-1 + 2*cos(pi/14)**2)*sin(pi/8) + sin(pi/7)*cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(15*pi/56) = sin(pi/7) * cos(pi/8) + sin(pi/8) * cos(pi/7),
{
have : sin(15*pi/56) = sin((pi/7) + (pi/8)),
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


lemma Trigo_number_generalization_step1_677 : sin(pi/42)*cos(pi/7) + sin(pi/7)*cos(pi/42)=1 / 2:=
begin
have : sin(pi/6) = sin(pi/42) * cos(pi/7) + sin(pi/7) * cos(pi/42),
{
have : sin(pi/6) = sin((pi/42) + (pi/7)),
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


lemma Trigo_number_generalization_step1_678 : -sin(pi/4) + sin(12214*pi/9)=2 * sin(-13*pi/72) * cos(5*pi/72):=
begin
have : sin(12214 * pi / 9) - sin(pi / 4) = -sin(pi/4) + sin(12214*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = sin(12214*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/9) (678),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) - sin(pi/4) = 2 * sin(-13*pi/72) * cos(5*pi/72),
{
rw sin_sub_sin,
have : cos(((-pi/9) + (pi/4))/2) = cos(5*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/9) - (pi/4))/2) = sin(-13*pi/72),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_679 (h0 : cos(3*pi/40)≠ 0) (h1 : cos(pi/5)≠ 0) (h2 : (tan(3*pi/40)*tan(pi/5)+1)≠ 0) (h3 : (1+tan(3*pi/40)*tan(pi/5))≠ 0) : (-tan(pi/5) + tan(3*pi/40))/(tan(3*pi/40)*tan(pi/5) + 1)=- 1 / tan(5195*pi/8):=
begin
have : (tan(3 * pi / 40) - tan(pi / 5)) / (1 + tan(3 * pi / 40) * tan(pi / 5)) = (-tan(pi/5) + tan(3*pi/40))/(tan(3*pi/40)*tan(pi/5) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = ( tan(3*pi/40) - tan(pi/5) ) / ( 1 + tan(3*pi/40) * tan(pi/5) ),
{
have : tan(-pi/8) = tan((3*pi/40) - (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - 1 / tan(5195*pi/8),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/8) (649),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_680 : sin(2726*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(2726*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (454),
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


lemma Trigo_number_generalization_step1_681 : -cos(5901*pi/8)=cos(6123*pi/8):=
begin
have : sin(-pi/8) = -cos(5901*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (368),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/8) = cos(6123*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (382),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_682 : cos(8624*pi/5)**2=1 - sin(-pi/5) ** 2:=
begin
have : (-cos(8624 * pi / 5)) ** 2 = cos(8624*pi/5)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) = -cos(8624*pi/5),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/5) (862),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/5) ** 2 = 1 - sin(-pi/5) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_683 : -sin(-3*pi/10)*sin(-pi/5) + cos(-3*pi/10)*cos(-pi/5)=sin(875*pi):=
begin
have : -sin((-3) * pi / 10) * sin(-pi / 5) + cos((-3) * pi / 10) * cos(-pi / 5) = -sin(-3*pi/10)*sin(-pi/5) + cos(-3*pi/10)*cos(-pi/5),
{
field_simp at *,
},
have : cos(-pi/2) = -sin(-3*pi/10) * sin(-pi/5) + cos(-3*pi/10) * cos(-pi/5),
{
have : cos(-pi/2) = cos((-3*pi/10) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(875*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (437),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_684 : -tan(2569*pi/3)=- tan(790*pi/3):=
begin
have : tan(-pi/3) = -tan(2569*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (856),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - tan(790*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (263),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_685 : cos(pi/3) - cos(-pi/7)=2*sin(5*pi/21)*sin(31582*pi/21):=
begin
have : (-2) * sin(5 * pi / 21) * -sin(31582 * pi / 21) = 2*sin(5*pi/21)*sin(31582*pi/21),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi/21) = -sin(31582*pi/21),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/21) (752),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) - cos(-pi/7) = - 2 * sin(5*pi/21) * sin(2*pi/21),
{
rw cos_sub_cos,
have : sin(((pi/3) + (-pi/7))/2) = sin(2*pi/21),
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
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_686 : cos(5452*pi/3)=- sin(4745*pi/6):=
begin
have : sin(-pi/6) = cos(5452*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (908),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(4745*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (395),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_687 : -cos(3898*pi/3)=1 / 2:=
begin
have : sin(pi/6) = -cos(3898*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (649),
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


lemma Trigo_number_generalization_step1_688 : cos(2273*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = cos(2273*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (283),
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


lemma Trigo_number_generalization_step1_689 : -sin(7973*pi/10)=sin(43*pi/10):=
begin
have : cos(pi/5) = -sin(7973*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/5) = sin(43*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/5) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_690 : -3*cos(pi/9) + 4*cos(pi/9)**3=1 / 2:=
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_691 : sin(pi/8) * sin(-pi/8)=-cos(0)/2 + sin(-pi/3)*sin(-pi/12)/2 + cos(-pi/3)*cos(-pi/12)/2:=
begin
have : (sin(-pi / 12) * sin(-pi / 3) + cos(-pi / 12) * cos(-pi / 3)) / 2 - cos(0) / 2 = -cos(0)/2 + sin(-pi/3)*sin(-pi/12)/2 + cos(-pi/3)*cos(-pi/12)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/4) = sin(-pi/12) * sin(-pi/3) + cos(-pi/12) * cos(-pi/3),
{
have : cos(pi/4) = cos((-pi/12) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/8) * sin(-pi/8) = cos(pi/4) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
have : cos((pi/8) + (-pi/8)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/8) - (-pi/8)) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_692 :-cos(4069*pi/14)=- cos(14635*pi/14):=
begin
have : sin(pi/7) = -cos(4069*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/7) (145),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = - cos(14635*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (522),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_693 : -sin(2050*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -sin(2050*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (341),
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


lemma Trigo_number_generalization_step1_694 : sin(pi/8) - sin(7*pi/6)=2 * sin(7*pi/48) * cos(-pi/48):=
begin
have : sin(-pi/6) = sin(7*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) - sin(-pi/6) = 2 * sin(7*pi/48) * cos(-pi/48),
{
rw sin_sub_sin,
have : cos(((pi/8) + (-pi/6))/2) = cos(-pi/48),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/8) - (-pi/6))/2) = sin(7*pi/48),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_695 : -sin(3535*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = -sin(3535*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/6) (295),
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


lemma Trigo_number_generalization_step1_696 : -cos(4971*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(4971*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (621),
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


lemma Trigo_number_generalization_step1_697 : cos(701*pi/2)=0:=
begin
have : sin(pi) = cos(701*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (174),
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


lemma Trigo_number_generalization_step1_698 : -sin(2869*pi/4)*cos(pi/3)=sin(-pi/12) / 2 + sin(7*pi/12) / 2:=
begin
have : sin(pi/4) = -sin(2869*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (358),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) * cos(pi/3) = sin(-pi/12) / 2 + sin(7*pi/12) / 2,
{
rw sin_mul_cos,
have : sin((pi/4) + (pi/3)) = sin(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/4) - (pi/3)) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_699 : -sin(5407*pi/6)=1 / 2:=
begin
have : sin(pi/6) = -sin(5407*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (450),
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


lemma Trigo_number_generalization_step1_700 : cos(15941*pi/14)**2 + cos(-pi/7)**2=1:=
begin
have : sin(-pi/7) = cos(15941*pi/14),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (569),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) ** 2 + cos(-pi/7) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_701 (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/4)≠ 0) (h2 : (tan(-pi/4)*tan(-pi/6)+1)≠ 0) (h3 : (1+tan(-pi/6)*tan(-pi/4))≠ 0) : (tan(-pi/6) - tan(-pi/4))/(tan(-pi/4)*tan(-pi/6) + 1)=2 - sqrt( 3 ):=
begin
have : (tan(-pi / 6) - tan(-pi / 4)) / (1 + tan(-pi / 6) * tan(-pi / 4)) = (tan(-pi/6) - tan(-pi/4))/(tan(-pi/4)*tan(-pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(-pi/6) - tan(-pi/4) ) / ( 1 + tan(-pi/6) * tan(-pi/4) ),
{
have : tan(pi/12) = tan((-pi/6) - (-pi/4)),
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


lemma Trigo_number_generalization_step1_702 : -sin(11101*pi/6)=- 1 / 2:=
begin
have : cos(2*pi/3) = -sin(11101*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (924),
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


lemma Trigo_number_generalization_step1_703 : sin(13*pi/7)=(1 - 2*sin(-pi)**2)*sin(-pi/7) - sin(-2*pi)*cos(-pi/7):=
begin
have : sin(-pi / 7) * (1 - 2 * sin(-pi) ** 2) - sin((-2) * pi) * cos(-pi / 7) = (1 - 2*sin(-pi)**2)*sin(-pi/7) - sin(-2*pi)*cos(-pi/7),
{
field_simp at *,
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
conv {to_rhs, rw ← this,},
have : sin(13*pi/7) = sin(-pi/7) * cos(-2*pi) - sin(-2*pi) * cos(-pi/7),
{
have : sin(13*pi/7) = sin((-pi/7) - (-2*pi)),
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


lemma Trigo_number_generalization_step1_704 : -sin(pi/6)**2 + cos(pi/6)**2=cos(3161*pi/3):=
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
have : cos(pi/3) = cos(3161*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (527),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_705 : cos(-pi) - sin(pi/8)**2 + cos(pi/8)**2=2 * cos(5*pi/8) * cos(-3*pi/8):=
begin
have : -sin(pi / 8) ** 2 + cos(pi / 8) ** 2 + cos(-pi) = cos(-pi) - sin(pi/8)**2 + cos(pi/8)**2,
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
have : cos(pi/4) + cos(-pi) = 2 * cos(5*pi/8) * cos(-3*pi/8),
{
rw cos_add_cos,
have : cos(((pi/4) + (-pi))/2) = cos(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/4) - (-pi))/2) = cos(5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_706 : -sin(-pi/8)**2 + cos(-pi/8)**2=2 * cos(-pi/8) ** 2 - 1:=
begin
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


lemma Trigo_number_generalization_step1_707 (h0 : cos((pi/3)/2)≠ 0) (h1 : (1+cos(pi/3))≠ 0) (h2 : (cos(pi/3)+1)≠ 0) : sin(pi/3)/(cos(pi/3) + 1)=tan(1453*pi/6):=
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
have : tan(pi/6) = tan(1453*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (242),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_708 (h0 : tan(1961*pi/2)≠ 0) : -1/tan(1961*pi/2)=0:=
begin
have : (-1) / tan(1961 * pi / 2) = -1/tan(1961*pi/2),
{
field_simp at *,
},
have : tan(pi) = -1 / tan(1961*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (979),
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


lemma Trigo_number_generalization_step1_709 : (-1 + 2*cos(-pi/4)**2)**2=cos(-pi) / 2 + 1 / 2:=
begin
have : (2 * cos(-pi / 4) ** 2 - 1) ** 2 = (-1 + 2*cos(-pi/4)**2)**2,
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
have : cos(-pi/2) ** 2 = cos(-pi) / 2 + 1 / 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
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


lemma Trigo_number_generalization_step1_710 : -sin(20515*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -sin(20515*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (854),
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


lemma Trigo_number_generalization_step1_711 : -cos(3815*pi/3)=sin(11111*pi/6):=
begin
have : sin(-pi/6) = -cos(3815*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (635),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(11111*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (926),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_712 : cos(949*pi/3)=1 / 2:=
begin
have : sin(pi/6) = cos(949*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (158),
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


lemma Trigo_number_generalization_step1_713 : -sin(3388*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -sin(3388*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/3) (565),
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


lemma Trigo_number_generalization_step1_714 : cos(5937*pi/8)=cos(6863*pi/8):=
begin
have : cos(pi/8) = cos(5937*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/8) (371),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = cos(6863*pi/8),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/8) (429),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_715 : sin(15155*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = sin(15155*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (631),
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


lemma Trigo_number_generalization_step1_716 : -3*cos(pi/15) + 4*cos(pi/15)**3=- cos(1134*pi/5):=
begin
have : 4 * cos(pi / 15) ** 3 - 3 * cos(pi / 15) = -3*cos(pi/15) + 4*cos(pi/15)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : cos(pi/5) = - cos(1134*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/5) (113),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_717 : cos(929*pi)=- 1:=
begin
have : cos(pi) = cos(929*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (465),
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


lemma Trigo_number_generalization_step1_718 : -cos(7639*pi/4)=sin(7143*pi/4):=
begin
have : sin(-pi/4) = -cos(7639*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (954),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(7143*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/4) (893),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_719 : cos(1319*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(1319*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (110),
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


lemma Trigo_number_generalization_step1_720 : -sin(-pi/4)**2 + cos(-pi/4)**2=2 * cos(-pi/4) ** 2 - 1:=
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


lemma Trigo_number_generalization_step1_721 : -tan(5849*pi/9)=- tan(5615*pi/9):=
begin
have : tan(pi/9) = -tan(5849*pi/9),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/9) (650),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = - tan(5615*pi/9),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/9) (624),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_722 : -tan(805*pi)=1 / tan(1361*pi/2):=
begin
have : tan(-2*pi) = -tan(805*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-2*pi) (803),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = 1 / tan(1361*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-2*pi) (678),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_724 : cos(938*pi)=- sin(1835*pi/2):=
begin
have : cos(-2*pi) = cos(938*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi) (470),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - sin(1835*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (459),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_725 : sin(19*pi/9)=-sin(-2*pi)*cos(1871*pi/9) + sin(pi/9)*cos(-2*pi):=
begin
have : sin(pi / 9) * cos((-2) * pi) - sin((-2) * pi) * cos(1871 * pi / 9) = -sin(-2*pi)*cos(1871*pi/9) + sin(pi/9)*cos(-2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) = cos(1871*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (104),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(19*pi/9) = sin(pi/9) * cos(-2*pi) - sin(-2*pi) * cos(pi/9),
{
have : sin(19*pi/9) = sin((pi/9) - (-2*pi)),
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


lemma Trigo_number_generalization_step1_726 : -cos(2284*pi/3)=1 / 2:=
begin
have : sin(pi/6) = -cos(2284*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (380),
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


lemma Trigo_number_generalization_step1_727 : (1 - 2*sin(-pi/2)**2)**2=cos(-2*pi) / 2 + 1 / 2:=
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


lemma Trigo_number_generalization_step1_728 : sin(-pi/12)*cos(-pi/3) - sin(-pi/3)*cos(-pi/12)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = sin(-pi/12) * cos(-pi/3) - sin(-pi/3) * cos(-pi/12),
{
have : sin(pi/4) = sin((-pi/12) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_729 : sin(-pi/5)*cos(-pi/20) + sin(-pi/20)*cos(-pi/5) + sin(-pi)=2 * sin(-5*pi/8) * cos(-3*pi/8):=
begin
have : sin(-pi) + (sin(-pi / 20) * cos(-pi / 5) + sin(-pi / 5) * cos(-pi / 20)) = sin(-pi/5)*cos(-pi/20) + sin(-pi/20)*cos(-pi/5) + sin(-pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = sin(-pi/20) * cos(-pi/5) + sin(-pi/5) * cos(-pi/20),
{
have : sin(-pi/4) = sin((-pi/20) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) + sin(-pi/4) = 2 * sin(-5*pi/8) * cos(-3*pi/8),
{
rw sin_add_sin,
have : sin(((-pi) + (-pi/4))/2) = sin(-5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (-pi/4))/2) = cos(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_730 : cos(pi/6) ** 2=1 - cos(799*pi/3)**2:=
begin
have : sin(pi/6) = cos(799*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (133),
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


lemma Trigo_number_generalization_step1_731 : cos(-2*pi)*cos(3*pi) - sin(-2*pi)*sin(3*pi)=- cos(1666*pi):=
begin
have : -sin(3 * pi) * sin((-2) * pi) + cos(3 * pi) * cos((-2) * pi) = cos(-2*pi)*cos(3*pi) - sin(-2*pi)*sin(3*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(3*pi) * sin(-2*pi) + cos(3*pi) * cos(-2*pi),
{
have : cos(pi) = cos((3*pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(1666*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (833),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_732 : sin(4151*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = sin(4151*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (519),
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


lemma Trigo_number_generalization_step1_733 : sin(-pi/7)*sin(47*pi/210) + cos(-pi/7)*cos(47*pi/210)=sin(pi/6) * sin(-pi/5) + cos(pi/6) * cos(-pi/5):=
begin
have : sin(47 * pi / 210) * sin(-pi / 7) + cos(47 * pi / 210) * cos(-pi / 7) = sin(-pi/7)*sin(47*pi/210) + cos(-pi/7)*cos(47*pi/210),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/30) = sin(47*pi/210) * sin(-pi/7) + cos(47*pi/210) * cos(-pi/7),
{
have : cos(11*pi/30) = cos((47*pi/210) - (-pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/30) = sin(pi/6) * sin(-pi/5) + cos(pi/6) * cos(-pi/5),
{
have : cos(11*pi/30) = cos((pi/6) - (-pi/5)),
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


lemma Trigo_number_generalization_step1_734 : -sin(3549*pi/8)*cos(pi/3)=cos(-11*pi/24) / 2 + cos(5*pi/24) / 2:=
begin
have : cos(-pi/8) = -sin(3549*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (221),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) * cos(pi/3) = cos(-11*pi/24) / 2 + cos(5*pi/24) / 2,
{
rw cos_mul_cos,
have : cos((-pi/8) + (pi/3)) = cos(5*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/8) - (pi/3)) = cos(-11*pi/24),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_735 : cos(pi/3)**2 + (-sin(2*pi)*cos(7*pi/3) + sin(7*pi/3)*cos(2*pi))**2=1:=
begin
have : (sin(7 * pi / 3) * cos(2 * pi) - sin(2 * pi) * cos(7 * pi / 3)) ** 2 + cos(pi / 3) ** 2 = cos(pi/3)**2 + (-sin(2*pi)*cos(7*pi/3) + sin(7*pi/3)*cos(2*pi))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(7*pi/3) * cos(2*pi) - sin(2*pi) * cos(7*pi/3),
{
have : sin(pi/3) = sin((7*pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) ** 2 + cos(pi/3) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_736 : -tan(1559*pi/4)=1:=
begin
have : tan(pi/4) = -tan(1559*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (390),
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


lemma Trigo_number_generalization_step1_737 (h0 : sin(10*pi)≠ 0) : tan(pi/2)=sin(pi/2)/sin(10*pi):=
begin
have : cos(pi/2) = sin(10*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(pi/2) = sin(pi/2) / cos(pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_738 (h0 : (1-2*sin(-pi/12)**2)≠ 0) : sin(-pi/6)/(1 - 2*sin(-pi/12)**2)=tan(-pi/6):=
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
have : sin(-pi/6) / cos(-pi/6) = tan(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_739 : (-3*cos(-pi/12) + 4*cos(-pi/12)**3)*cos(pi/3)=cos(7*pi/12) / 2 + cos(pi/12) / 2:=
begin
have : cos(pi / 3) * (4 * cos(-pi / 12) ** 3 - 3 * cos(-pi / 12)) = (-3*cos(-pi/12) + 4*cos(-pi/12)**3)*cos(pi/3),
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
have : cos(pi/3) * cos(-pi/4) = cos(7*pi/12) / 2 + cos(pi/12) / 2,
{
rw cos_mul_cos,
have : cos((pi/3) + (-pi/4)) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (-pi/4)) = cos(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_740 (h0 : cos((2*pi/9)/2)≠ 0) (h1 : sin(2*pi/9)≠ 0) : (1 - cos(2*pi/9))/sin(2*pi/9)=tan(7741*pi/9):=
begin
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
have : tan(pi/9) = tan(7741*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (860),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_741 (h0 : cos(pi/12)≠ 0) (h1 : (2*cos(pi/12))≠ 0) : sin(pi/6)/(2*cos(pi/12))=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = sin(pi/6) / ( 2 * cos(pi/12) ),
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
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_number_generalization_step1_742 : sin(2*pi/3)=-(1 - 2*sin(-pi/6)**2)*sin(-pi) + sin(-pi/3)*cos(-pi):=
begin
have : sin(-pi / 3) * cos(-pi) - sin(-pi) * (1 - 2 * sin(-pi / 6) ** 2) = -(1 - 2*sin(-pi/6)**2)*sin(-pi) + sin(-pi/3)*cos(-pi),
{
field_simp at *,
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
have : sin(2*pi/3) = sin(-pi/3) * cos(-pi) - sin(-pi) * cos(-pi/3),
{
have : sin(2*pi/3) = sin((-pi/3) - (-pi)),
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


lemma Trigo_number_generalization_step1_743 (h0 : tan(1766*pi/3)≠ 0) : -1/tan(1766*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(1766 * pi / 3) = -1/tan(1766*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(1766*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (588),
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


lemma Trigo_number_generalization_step1_744 : -sin(3859*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -sin(3859*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (160),
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


lemma Trigo_number_generalization_step1_745 : 1 - 2*sin(-pi/12)**2=cos(7861*pi/6):=
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
have : cos(-pi/6) = cos(7861*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (655),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_746 : cos(2341*pi/2)=- sin(-pi) * sin(-pi/2) + cos(-pi) * cos(-pi/2):=
begin
have : cos(-3*pi/2) = cos(2341*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-3*pi/2) (586),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = - sin(-pi) * sin(-pi/2) + cos(-pi) * cos(-pi/2),
{
have : cos(-3*pi/2) = cos((-pi) + (-pi/2)),
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


lemma Trigo_number_generalization_step1_747 (h0 : cos(pi/2)≠ 0) : -cos(1443*pi)/cos(pi/2)=tan(pi/2):=
begin
have : sin(pi/2) = -cos(1443*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (721),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) / cos(pi/2) = tan(pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_748 : sin(pi/6)*cos(-pi/6) - sin(-pi/6)*cos(pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(pi/6) * cos(-pi/6) - sin(-pi/6) * cos(pi/6),
{
have : sin(pi/3) = sin((pi/6) - (-pi/6)),
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


lemma Trigo_number_generalization_step1_749 : sin(pi/9)*cos(7*pi/18) + sin(7*pi/18)*cos(pi/9)=1:=
begin
have : sin(7 * pi / 18) * cos(pi / 9) + sin(pi / 9) * cos(7 * pi / 18) = sin(pi/9)*cos(7*pi/18) + sin(7*pi/18)*cos(pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(7*pi/18) * cos(pi/9) + sin(pi/9) * cos(7*pi/18),
{
have : sin(pi/2) = sin((7*pi/18) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_number_generalization_step1_750 (h0 : cos(pi/3)≠ 0) (h1 : (1-tan(pi/3)**2)≠ 0) : 2*tan(pi/3)/(1 - tan(pi/3)**2)=- sqrt( 3 ):=
begin
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


lemma Trigo_number_generalization_step1_751 : -cos(1417*pi/2)=sin(1350*pi):=
begin
have : sin(-2*pi) = -cos(1417*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (355),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(1350*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (676),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_752 (h0 : cos(-pi/12)≠ 0) (h1 : (1-tan(-pi/12)**2)≠ 0) : sin(-pi/6) / cos(-pi/6)=2*tan(-pi/12)/(1 - tan(-pi/12)**2):=
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
conv {to_rhs, rw ← this,},
have : sin(-pi/6) / cos(-pi/6) = tan(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_753 : cos(1727*pi/10)**2=1 - cos(-pi/5) ** 2:=
begin
have : sin(-pi/5) = cos(1727*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/5) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) ** 2 = 1 - cos(-pi/5) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_754 : -cos(25345*pi/14)=- sin(14006*pi/7):=
begin
have : sin(-pi/7) = -cos(25345*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/7) (905),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = - sin(14006*pi/7),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/7) (1000),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_755 (h0 : cos(-pi)≠ 0) (h1 : (1-tan(-pi)**2)≠ 0) : 2*tan(-pi)/(1 - tan(-pi)**2)=1 / tan(1973*pi/2):=
begin
have : tan(-2*pi) = 2 * tan(-pi) / ( 1 - tan(-pi) ** 2 ),
{
have : tan(-2*pi) = tan(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = 1 / tan(1973*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-2*pi) (984),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_756 : -sin(-2*pi)*sin(9*pi/4) + cos(-2*pi)*cos(9*pi/4)=sqrt( 2 ) / 2:=
begin
have : -sin(9 * pi / 4) * sin((-2) * pi) + cos(9 * pi / 4) * cos((-2) * pi) = -sin(-2*pi)*sin(9*pi/4) + cos(-2*pi)*cos(9*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(9*pi/4) * sin(-2*pi) + cos(9*pi/4) * cos(-2*pi),
{
have : cos(pi/4) = cos((9*pi/4) + (-2*pi)),
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


lemma Trigo_number_generalization_step1_757 (h0 : tan(1919*pi/6)≠ 0) : 1/tan(1919*pi/6)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = 1 / tan(1919*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (320),
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


lemma Trigo_number_generalization_step1_758 : -sin(3668*pi/3) + cos(2*pi)=- 2 * sin(13*pi/12) * sin(11*pi/12):=
begin
have : cos(2 * pi) - sin(3668 * pi / 3) = -sin(3668*pi/3) + cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(3668*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (611),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_759 : cos(-pi/2)*cos(5*pi/6) - sin(-pi/2)*sin(5*pi/6)=1 / 2:=
begin
have : -sin(5 * pi / 6) * sin(-pi / 2) + cos(5 * pi / 6) * cos(-pi / 2) = cos(-pi/2)*cos(5*pi/6) - sin(-pi/2)*sin(5*pi/6),
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_760 (h0 : cos((-2*pi/9)/2)≠ 0) (h1 : (1+cos((-2)*pi/9))≠ 0) (h2 : (cos(-2*pi/9)+1)≠ 0) : sin(-2*pi/9)/(cos(-2*pi/9) + 1)=- 1 / tan(5911*pi/18):=
begin
have : sin((-2) * pi / 9) / (1 + cos((-2) * pi / 9)) = sin(-2*pi/9)/(cos(-2*pi/9) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/9) = sin(-2*pi/9) / ( 1 + cos(-2*pi/9) ),
{
have : tan(-pi/9) = tan((-2*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/9) = - 1 / tan(5911*pi/18),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/9) (328),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_761 : cos(7247*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(7247*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (604),
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


lemma Trigo_number_generalization_step1_762 : cos(5025*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = cos(5025*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (628),
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


lemma Trigo_number_generalization_step1_763 : sin(-17*pi/30)*cos(-pi/6) - sin(-pi/6)*cos(-17*pi/30)=2 * sin(-pi/5) * cos(-pi/5):=
begin
have : sin((-17) * pi / 30) * cos(-pi / 6) - sin(-pi / 6) * cos((-17) * pi / 30) = sin(-17*pi/30)*cos(-pi/6) - sin(-pi/6)*cos(-17*pi/30),
{
field_simp at *,
},
have : sin(-2*pi/5) = sin(-17*pi/30) * cos(-pi/6) - sin(-pi/6) * cos(-17*pi/30),
{
have : sin(-2*pi/5) = sin((-17*pi/30) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_764 : -3*cos(-pi/9) + 4*cos(-pi/9)**3=2 * cos(-pi/6) ** 2 - 1:=
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


lemma Trigo_number_generalization_step1_765 : sin(5459*pi/6)**2=cos(-2*pi/3) / 2 + 1 / 2:=
begin
have : (-sin(5459 * pi / 6)) ** 2 = sin(5459*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(5459*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (454),
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


lemma Trigo_number_generalization_step1_766 : -sin(5993*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -sin(5993*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (249),
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


lemma Trigo_number_generalization_step1_767 : -cos(-pi/9) - sin(6491*pi/14)=- 2 * sin(-pi/63) * sin(-8*pi/63):=
begin
have : -sin(6491 * pi / 14) - cos(-pi / 9) = -cos(-pi/9) - sin(6491*pi/14),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = -sin(6491*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (231),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) - cos(-pi/9) = - 2 * sin(-pi/63) * sin(-8*pi/63),
{
rw cos_sub_cos,
have : sin(((-pi/7) + (-pi/9))/2) = sin(-8*pi/63),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/7) - (-pi/9))/2) = sin(-pi/63),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_768 : sin(pi/3)=-sin(-1844*pi/3):=
begin
have : -sin((-1844) * pi / 3) = -sin(-1844*pi/3),
{
field_simp at *,
},
have : cos(11731*pi/6) = sin(-1844*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11731*pi/6) (670),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = - cos(11731*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (977),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_769 (h0 : cos(pi/10)≠ 0) (h1 : (1-tan(pi/10)**2)≠ 0) : 2*tan(pi/10)/(1 - tan(pi/10)**2)=1 / tan(2393*pi/10):=
begin
have : tan(pi/5) = 2 * tan(pi/10) / ( 1 - tan(pi/10) ** 2 ),
{
have : tan(pi/5) = tan(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/5) = 1 / tan(2393*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/5) (239),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_770 (h0 : cos(-7*pi/60)≠ 0) (h1 : cos(-pi/5)≠ 0) (h2 : (tan(-pi/5)*tan(-7*pi/60)+1)≠ 0) (h3 : (1+tan((-7)*pi/60)*tan(-pi/5))≠ 0) : (tan(-7*pi/60) - tan(-pi/5))/(tan(-pi/5)*tan(-7*pi/60) + 1)=2 - sqrt( 3 ):=
begin
have : (tan((-7) * pi / 60) - tan(-pi / 5)) / (1 + tan((-7) * pi / 60) * tan(-pi / 5)) = (tan(-7*pi/60) - tan(-pi/5))/(tan(-pi/5)*tan(-7*pi/60) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = ( tan(-7*pi/60) - tan(-pi/5) ) / ( 1 + tan(-7*pi/60) * tan(-pi/5) ),
{
have : tan(pi/12) = tan((-7*pi/60) - (-pi/5)),
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


lemma Trigo_number_generalization_step1_771 : sin(-pi/6)=-cos(-pi/6)*cos(1031*pi/6) + sin(-pi/6)*sin(1031*pi/6):=
begin
have : -(-sin(1031 * pi / 6) * sin(-pi / 6) + cos(1031 * pi / 6) * cos(-pi / 6)) = -cos(-pi/6)*cos(1031*pi/6) + sin(-pi/6)*sin(1031*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(515*pi/3) = -sin(1031*pi/6) * sin(-pi/6) + cos(1031*pi/6) * cos(-pi/6),
{
have : cos(515*pi/3) = cos((1031*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = - cos(515*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_772 : sin(24145*pi/14)=- cos(10534*pi/7):=
begin
have : cos(pi/7) = sin(24145*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/7) (862),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = - cos(10534*pi/7),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/7) (752),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_773 : sin(2*pi/15)*cos(pi/5) + sin(pi/5)*cos(2*pi/15)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = sin(2*pi/15) * cos(pi/5) + sin(pi/5) * cos(2*pi/15),
{
have : sin(pi/3) = sin((2*pi/15) + (pi/5)),
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


lemma Trigo_number_generalization_step1_774 : cos(-pi/7)=-sin(pi/9)*cos(150791*pi/126) + sin(150791*pi/126)*cos(pi/9):=
begin
have : sin(150791 * pi / 126) * cos(pi / 9) - sin(pi / 9) * cos(150791 * pi / 126) = -sin(pi/9)*cos(150791*pi/126) + sin(150791*pi/126)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(16753*pi/14) = sin(150791*pi/126) * cos(pi/9) - sin(pi/9) * cos(150791*pi/126),
{
have : sin(16753*pi/14) = sin((150791*pi/126) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/7) = sin(16753*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/7) (598),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_775 : -cos(3149*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(3149*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (393),
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


lemma Trigo_number_generalization_step1_776 : -sin(1324*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -sin(1324*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/3) (221),
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


lemma Trigo_number_generalization_step1_777 : -tan(1286*pi/3)=1 / tan(2233*pi/6):=
begin
have : tan(pi/3) = -tan(1286*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (429),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(2233*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (372),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_778 : cos(9347*pi/14)=sin(3669*pi/7):=
begin
have : sin(pi/7) = cos(9347*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (333),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(3669*pi/7),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/7) (262),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_779 : -cos(1705*pi/2)=0:=
begin
have : sin(pi) = -cos(1705*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (426),
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


lemma Trigo_number_generalization_step1_780 : cos(pi/6)=sin(4417*pi/3):=
begin
have : - -sin(4417 * pi / 3) = sin(4417*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1240*pi/3) = -sin(4417*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1240*pi/3) (529),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = - sin(1240*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (206),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_781 : -cos(145*pi/3)=- 1 / 2:=
begin
have : cos(2*pi/3) = -cos(145*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (24),
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


lemma Trigo_number_generalization_step1_782 : sin(pi/6)*sin(pi/4) + cos(pi/6)*cos(pi/4)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
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


lemma Trigo_number_generalization_step1_783 (h0 : (-3*cos(pi/3)+4*cos(pi/3)**3)≠ 0) (h1 : (4*cos(pi/3)**3-3*cos(pi/3))≠ 0) : tan(pi)=sin(pi)/(-3*cos(pi/3) + 4*cos(pi/3)**3):=
begin
have : sin(pi) / (4 * cos(pi / 3) ** 3 - 3 * cos(pi / 3)) = sin(pi)/(-3*cos(pi/3) + 4*cos(pi/3)**3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_784 : sin(pi/2)=-sin(0) + sin(pi/2):=
begin
have : 2 * (-sin(0) / 2 + sin(pi / 2) / 2) = -sin(0) + sin(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) * cos(pi/4) = -sin(0) / 2 + sin(pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/4) + (pi/4)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/4) - (pi/4)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(pi/4) * cos(pi/4)) = 2*sin(pi/4)*cos(pi/4),
{
ring,
},
conv {to_rhs, rw this,},
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
rw this,
end


lemma Trigo_number_generalization_step1_785 : cos(5111*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = cos(5111*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (425),
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


lemma Trigo_number_generalization_step1_786 : 4*sin(pi/2)**2*cos(pi/2)**2=1 / 2 - cos(2*pi) / 2:=
begin
have : (2 * sin(pi / 2) * cos(pi / 2)) ** 2 = 4*sin(pi/2)**2*cos(pi/2)**2,
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
have : sin(pi) ** 2 = 1 / 2 - cos(2*pi) / 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_787 : -sin(8227*pi/10)=sin(-pi/2) * cos(pi/5) - sin(pi/5) * cos(-pi/2):=
begin
have : sin(-7*pi/10) = -sin(8227*pi/10),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-7*pi/10) (411),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/10) = sin(-pi/2) * cos(pi/5) - sin(pi/5) * cos(-pi/2),
{
have : sin(-7*pi/10) = sin((-pi/2) - (pi/5)),
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


lemma Trigo_number_generalization_step1_788 (h0 : tan(447*pi/4)≠ 0) : -1/tan(447*pi/4)=1:=
begin
have : (-1) / tan(447 * pi / 4) = -1/tan(447*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(447*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (111),
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


lemma Trigo_number_generalization_step1_789 : cos(2*pi/9)=1 - 2*sin(pi/9)**2:=
begin
have : -sin(pi / 9) ** 2 + (1 - sin(pi / 9) ** 2) = 1 - 2*sin(pi/9)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) ** 2 = 1 - sin(pi/9) ** 2,
{
rw cos_sq',
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


lemma Trigo_number_generalization_step1_790 (h0 : cos(-2*pi/5)≠ 0) (h1 : (2*cos(-2*pi/5))≠ 0) (h2 : (2*cos((-2)*pi/5))≠ 0) : sin(-4*pi/5)/(2*cos(-2*pi/5))=2 * sin(-pi/5) * cos(-pi/5):=
begin
have : sin((-4) * pi / 5) / (2 * cos((-2) * pi / 5)) = sin(-4*pi/5)/(2*cos(-2*pi/5)),
{
field_simp at *,
},
have : sin(-2*pi/5) = sin(-4*pi/5) / ( 2 * cos(-2*pi/5) ),
{
have : sin(-4*pi/5) = sin(2*(-2*pi/5)),
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


lemma Trigo_number_generalization_step1_791 : cos(-pi/4)=1 - 2*cos(8187*pi/8)**2:=
begin
have : sin(-pi/8) = cos(8187*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/8) (511),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_number_generalization_step1_792 : sin(5929*pi/6)=sin(469*pi/6):=
begin
have : sin(pi/6) = sin(5929*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (494),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(469*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_793 : -sin(37*pi/6)=- sin(pi/3) ** 2 + cos(pi/3) ** 2:=
begin
have : cos(2*pi/3) = -sin(37*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = - sin(pi/3) ** 2 + cos(pi/3) ** 2,
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
rw this,
end


lemma Trigo_number_generalization_step1_794 : -1 + 2*cos(pi/6)**2=sin(pi/6) * sin(-pi/6) + cos(pi/6) * cos(-pi/6):=
begin
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


lemma Trigo_number_generalization_step1_795 : -3*cos(-pi/12) + 4*cos(-pi/12)**3=- cos(1405*pi/4):=
begin
have : 4 * cos(-pi / 12) ** 3 - 3 * cos(-pi / 12) = -3*cos(-pi/12) + 4*cos(-pi/12)**3,
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
have : cos(-pi/4) = - cos(1405*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (175),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_796 : sin(7*pi/10)=-sin(pi/5)*sin(1080*pi) + sin(pi/2)*cos(pi/5):=
begin
have : sin(pi / 5) * -sin(1080 * pi) + sin(pi / 2) * cos(pi / 5) = -sin(pi/5)*sin(1080*pi) + sin(pi/2)*cos(pi/5),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -sin(1080*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (539),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(7*pi/10) = sin(pi/5) * cos(pi/2) + sin(pi/2) * cos(pi/5),
{
have : sin(7*pi/10) = sin((pi/5) + (pi/2)),
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


lemma Trigo_number_generalization_step1_797 : sin(-5*pi/12)=sin(-pi/4)*sin(5720*pi/3) + sin(-pi/6)*cos(-pi/4):=
begin
have : cos(-pi/6) = sin(5720*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (953),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/12) = sin(-pi/4) * cos(-pi/6) + sin(-pi/6) * cos(-pi/4),
{
have : sin(-5*pi/12) = sin((-pi/4) + (-pi/6)),
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


lemma Trigo_number_generalization_step1_798 : -sin(52241*pi/30)=- sin(pi/3) * sin(-pi/5) + cos(pi/3) * cos(-pi/5):=
begin
have : cos(2*pi/15) = -sin(52241*pi/30),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/15) (870),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/15) = - sin(pi/3) * sin(-pi/5) + cos(pi/3) * cos(-pi/5),
{
have : cos(2*pi/15) = cos((pi/3) + (-pi/5)),
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


lemma Trigo_number_generalization_step1_799 : sin(pi/6)**2 + (-sin(-pi/30)*sin(pi/5) + cos(-pi/30)*cos(pi/5))**2=1:=
begin
have : cos(pi/6) = -sin(-pi/30) * sin(pi/5) + cos(-pi/30) * cos(pi/5),
{
have : cos(pi/6) = cos((-pi/30) + (pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 + cos(pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_800 (h0 : tan(3053*pi/6)≠ 0) : -1/tan(3053*pi/6)=sqrt( 3 ):=
begin
have : (-1) / tan(3053 * pi / 6) = -1/tan(3053*pi/6),
{
field_simp at *,
},
have : tan(pi/3) = -1 / tan(3053*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (508),
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


lemma Trigo_number_generalization_step1_801 : sin(-pi/3)=-2*sin(-pi/6)*sin(4997*pi/3):=
begin
have : 2 * sin(-pi / 6) * -sin(4997 * pi / 3) = -2*sin(-pi/6)*sin(4997*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(4997*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (832),
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


lemma Trigo_number_generalization_step1_802 (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : sin(pi)/(2*sin(pi/2))=cos(2073*pi/2):=
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
have : cos(pi/2) = cos(2073*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (518),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_803 : sin(-pi/12)*sin(pi/4) + cos(-pi/12)*cos(pi/4)=4 * cos(-pi/9) ** 3 - 3 * cos(-pi/9):=
begin
have : cos(-pi/3) = sin(-pi/12) * sin(pi/4) + cos(-pi/12) * cos(pi/4),
{
have : cos(-pi/3) = cos((-pi/12) - (pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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
rw this,
end


lemma Trigo_number_generalization_step1_804 : -sin(-pi/2)*sin(4*pi/3) + cos(-pi/2)*cos(4*pi/3)=- sqrt( 3 ) / 2:=
begin
have : -sin(4 * pi / 3) * sin(-pi / 2) + cos(4 * pi / 3) * cos(-pi / 2) = -sin(-pi/2)*sin(4*pi/3) + cos(-pi/2)*cos(4*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(4*pi/3) * sin(-pi/2) + cos(4*pi/3) * cos(-pi/2),
{
have : cos(5*pi/6) = cos((4*pi/3) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_805 : cos(59*pi/2)=2 * sin(pi/2) * cos(pi/2):=
begin
have : sin(pi) = cos(59*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (15),
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
rw this,
end


lemma Trigo_number_generalization_step1_806 : cos(-pi/6)=4*sin(2872*pi/9)**3 - 3*sin(2872*pi/9):=
begin
have : -((-4) * sin(2872 * pi / 9) ** 3 + 3 * sin(2872 * pi / 9)) = 4*sin(2872*pi/9)**3 - 3*sin(2872*pi/9),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2872*pi/3) = -4 * sin(2872*pi/9) ** 3 + 3 * sin(2872*pi/9),
{
have : sin(2872*pi/3) = sin(3*(2872*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(2872*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (478),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_807 : -sin(2*pi)*cos(-4*pi) + sin(-4*pi)*cos(2*pi)=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : sin((-4) * pi) * cos(2 * pi) - sin(2 * pi) * cos((-4) * pi) = -sin(2*pi)*cos(-4*pi) + sin(-4*pi)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-6*pi) = sin(-4*pi) * cos(2*pi) - sin(2*pi) * cos(-4*pi),
{
have : sin(-6*pi) = sin((-4*pi) - (2*pi)),
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


lemma Trigo_number_generalization_step1_808 : sin(-pi/2) * cos(pi/7)=sin(-pi/2)*cos(-pi/7):=
begin
have : 1 / 2 * (2 * sin(-pi / 2) * cos(-pi / 7)) = sin(-pi/2)*cos(-pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-9*pi/14) + sin(-5*pi/14) = 2 * sin(-pi/2) * cos(-pi/7),
{
rw sin_add_sin,
have : sin(((-9*pi/14) + (-5*pi/14))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-9*pi/14) - (-5*pi/14))/2) = cos(-pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 1/2*(sin(-9*pi/14) + sin(-5*pi/14)) = sin(-9*pi/14)/2+sin(-5*pi/14)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-pi/2) * cos(pi/7) = sin(-9*pi/14) / 2 + sin(-5*pi/14) / 2,
{
rw sin_mul_cos,
have : sin((-pi/2) + (pi/7)) = sin(-5*pi/14),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (pi/7)) = sin(-9*pi/14),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_809 : cos(-14*pi/45)=-(3*sin(-pi/27) - 4*sin(-pi/27)**3)*sin(-pi/5) + cos(-pi/5)*cos(-pi/9):=
begin
have : -sin(-pi / 5) * ((-4) * sin(-pi / 27) ** 3 + 3 * sin(-pi / 27)) + cos(-pi / 5) * cos(-pi / 9) = -(3*sin(-pi/27) - 4*sin(-pi/27)**3)*sin(-pi/5) + cos(-pi/5)*cos(-pi/9),
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
have : cos(-14*pi/45) = - sin(-pi/5) * sin(-pi/9) + cos(-pi/5) * cos(-pi/9),
{
have : cos(-14*pi/45) = cos((-pi/5) + (-pi/9)),
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


lemma Trigo_number_generalization_step1_810 : sin(0)*sin(-pi/3) + cos(0)*cos(-pi/3)=1 / 2:=
begin
have : cos(pi/3) = sin(0) * sin(-pi/3) + cos(0) * cos(-pi/3),
{
have : cos(pi/3) = cos((0) - (-pi/3)),
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


lemma Trigo_number_generalization_step1_811 : 1 - 2*sin(pi/3)**2=- 1 / 2:=
begin
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


lemma Trigo_number_generalization_step1_812 : cos(2627*pi/6)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = cos(2627*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (219),
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


lemma Trigo_number_generalization_step1_813 : -cos(8579*pi/14)=2 * sin(pi/7) * cos(pi/7):=
begin
have : sin(2*pi/7) = -cos(8579*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/7) (306),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/7) = 2 * sin(pi/7) * cos(pi/7),
{
have : sin(2*pi/7) = sin(2*(pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_814 : -tan(4061*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(pi/6) = -tan(4061*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (677),
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


lemma Trigo_number_generalization_step1_815 : sin(2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(2*pi)=1 / 2:=
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


lemma Trigo_number_generalization_step1_816 : sin(9203*pi/6)**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : (-sin(9203 * pi / 6)) ** 2 = sin(9203*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(9203*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (766),
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


lemma Trigo_number_generalization_step1_817 : (sin(-pi/5)*cos(-9*pi/5) + sin(-9*pi/5)*cos(-pi/5))*cos(-pi/7)=sin(-13*pi/7) / 2 + sin(-15*pi/7) / 2:=
begin
have : (sin((-9) * pi / 5) * cos(-pi / 5) + sin(-pi / 5) * cos((-9) * pi / 5)) * cos(-pi / 7) = (sin(-pi/5)*cos(-9*pi/5) + sin(-9*pi/5)*cos(-pi/5))*cos(-pi/7),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-9*pi/5) * cos(-pi/5) + sin(-pi/5) * cos(-9*pi/5),
{
have : sin(-2*pi) = sin((-9*pi/5) + (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step1_818 : -cos(179*pi)=1:=
begin
have : sin(pi/2) = -cos(179*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (89),
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


lemma Trigo_number_generalization_step1_819 (h0 : tan(315*pi/4)≠ 0) : 1/tan(315*pi/4)=- 1:=
begin
have : tan(3*pi/4) = 1 / tan(315*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (79),
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


lemma Trigo_number_generalization_step1_820 : cos(-pi/4) - cos(pi/8)=-cos(-pi/8) + cos(-pi/4):=
begin
have : (-2) * (cos(-pi / 8) / 2 - cos(-pi / 4) / 2) = -cos(-pi/8) + cos(-pi/4),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/16) * sin(-pi/16) = cos(-pi/8) / 2 - cos(-pi/4) / 2,
{
rw sin_mul_sin,
have : cos((-3*pi/16) + (-pi/16)) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-3*pi/16) - (-pi/16)) = cos(-pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -2*(sin(-3*pi/16) * sin(-pi/16)) = -2*sin(-3*pi/16)*sin(-pi/16),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-pi/4) - cos(pi/8) = - 2 * sin(-3*pi/16) * sin(-pi/16),
{
rw cos_sub_cos,
have : sin(((-pi/4) + (pi/8))/2) = sin(-pi/16),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/4) - (pi/8))/2) = sin(-3*pi/16),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_821 : cos(-pi/9)=cos(22645*pi/9):=
begin
have : sin(31655*pi/18) = cos(22645*pi/9),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (31655*pi/18) (378),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) = sin(31655*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/9) (879),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_822 : cos(0)=-(-sin(-pi/5)*cos(4*pi/5) + sin(4*pi/5)*cos(-pi/5))*sin(-pi) + cos(-pi)*cos(pi):=
begin
have : -sin(-pi) * (sin(4 * pi / 5) * cos(-pi / 5) - sin(-pi / 5) * cos(4 * pi / 5)) + cos(-pi) * cos(pi) = -(-sin(-pi/5)*cos(4*pi/5) + sin(4*pi/5)*cos(-pi/5))*sin(-pi) + cos(-pi)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = sin(4*pi/5) * cos(-pi/5) - sin(-pi/5) * cos(4*pi/5),
{
have : sin(pi) = sin((4*pi/5) - (-pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(0) = - sin(-pi) * sin(pi) + cos(-pi) * cos(pi),
{
have : cos(0) = cos((-pi) + (pi)),
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


lemma Trigo_number_generalization_step1_823 : cos(-pi/3) - cos(8396*pi/9)=2 * cos(pi/9) * cos(-2*pi/9):=
begin
have : -cos(8396 * pi / 9) + cos(-pi / 3) = cos(-pi/3) - cos(8396*pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) = -cos(8396*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/9) (466),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/9) + cos(-pi/3) = 2 * cos(pi/9) * cos(-2*pi/9),
{
rw cos_add_cos,
have : cos(((-pi/9) + (-pi/3))/2) = cos(-2*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/9) - (-pi/3))/2) = cos(pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_824 : (sin(-2*pi/9)*cos(-pi/9) + sin(-pi/9)*cos(-2*pi/9))**2=1 / 2 - cos(-2*pi/3) / 2:=
begin
have : (sin((-2) * pi / 9) * cos(-pi / 9) + sin(-pi / 9) * cos((-2) * pi / 9)) ** 2 = (sin(-2*pi/9)*cos(-pi/9) + sin(-pi/9)*cos(-2*pi/9))**2,
{
field_simp at *,
},
have : sin(-pi/3) = sin(-2*pi/9) * cos(-pi/9) + sin(-pi/9) * cos(-2*pi/9),
{
have : sin(-pi/3) = sin((-2*pi/9) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_number_generalization_step1_825 : tan(3862*pi/9)=tan(4411*pi/9):=
begin
have : tan(pi/9) = tan(3862*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (429),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = tan(4411*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (490),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_826 (h0 : sin(-pi/2)≠ 0) (h1 : (4*sin(-pi/2))≠ 0) (h2 : (2*sin(-pi/2))≠ 0) : sin(-pi/4) ** 2=-sin(-pi)/(4*sin(-pi/2)) + 1/2:=
begin
have : 1 / 2 - sin(-pi) / (2 * sin(-pi / 2)) / 2 = -sin(-pi)/(4*sin(-pi/2)) + 1/2,
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
have : sin(-pi/4) ** 2 = 1 / 2 - cos(-pi/2) / 2,
{
have : cos(-pi/2) = cos(2*(-pi/4)),
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


lemma Trigo_number_generalization_step1_827 (h0 : cos(-pi)≠ 0) (h1 : (1-tan(-pi)**2)≠ 0) : 2*tan(-pi)/(1 - tan(-pi)**2)=- tan(255*pi):=
begin
have : tan(-2*pi) = 2 * tan(-pi) / ( 1 - tan(-pi) ** 2 ),
{
have : tan(-2*pi) = tan(2*(-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = - tan(255*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-2*pi) (253),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_828 : cos(-pi/9)*cos(8*pi/9) + sin(-pi/9)*sin(8*pi/9)=- 1:=
begin
have : sin(8 * pi / 9) * sin(-pi / 9) + cos(8 * pi / 9) * cos(-pi / 9) = cos(-pi/9)*cos(8*pi/9) + sin(-pi/9)*sin(8*pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(8*pi/9) * sin(-pi/9) + cos(8*pi/9) * cos(-pi/9),
{
have : cos(pi) = cos((8*pi/9) - (-pi/9)),
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


lemma Trigo_number_generalization_step1_829 : sin(-pi/4)**2 + sin(6265*pi/4)**2=1:=
begin
have : cos(-pi/4) = sin(6265*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/4) (783),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) ** 2 + cos(-pi/4) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_830 : (-sin(pi/12)**2 + cos(pi/12)**2)**2=1 - sin(pi/6) ** 2:=
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
have : cos(pi/6) ** 2 = 1 - sin(pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_831 : cos(7521*pi/7)=4 * cos(pi/7) ** 3 - 3 * cos(pi/7):=
begin
have : cos(3*pi/7) = cos(7521*pi/7),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/7) (537),
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


lemma Trigo_number_generalization_step1_832 (h0 : cos(pi/8)≠ 0) (h1 : (1-tan(pi/8)**2)≠ 0) : 2*tan(pi/8)/(1 - tan(pi/8)**2)=1:=
begin
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


lemma Trigo_number_generalization_step1_833 : -cos(1429*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -cos(1429*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (119),
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


lemma Trigo_number_generalization_step1_834 : cos(-pi/2)=cos(pi/2)*cos(pi) + (sin(3*pi/4)*cos(-pi/4) + sin(-pi/4)*cos(3*pi/4))*sin(pi):=
begin
have : (sin(3 * pi / 4) * cos(-pi / 4) + sin(-pi / 4) * cos(3 * pi / 4)) * sin(pi) + cos(pi / 2) * cos(pi) = cos(pi/2)*cos(pi) + (sin(3*pi/4)*cos(-pi/4) + sin(-pi/4)*cos(3*pi/4))*sin(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(3*pi/4) * cos(-pi/4) + sin(-pi/4) * cos(3*pi/4),
{
have : sin(pi/2) = sin((3*pi/4) + (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(pi/2) * sin(pi) + cos(pi/2) * cos(pi),
{
have : cos(-pi/2) = cos((pi/2) - (pi)),
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


lemma Trigo_number_generalization_step1_835 : -tan(3251*pi/6)=- tan(5057*pi/6):=
begin
have : tan(pi/6) = -tan(3251*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (542),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = - tan(5057*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (843),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_836 : sin(5*pi/3)*sin(2*pi) + cos(5*pi/3)*cos(2*pi)=cos(2539*pi/3):=
begin
have : cos(-pi/3) = sin(5*pi/3) * sin(2*pi) + cos(5*pi/3) * cos(2*pi),
{
have : cos(-pi/3) = cos((5*pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(2539*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (423),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_837 (h0 : sin(-pi/9)≠ 0) (h1 : (4*sin(-pi/9)**2)≠ 0) (h2 : (2*sin(-pi/9))≠ 0) : sin(-2*pi/9)**2/(4*sin(-pi/9)**2)=cos(-2*pi/9) / 2 + 1 / 2:=
begin
have : (sin((-2) * pi / 9) / (2 * sin(-pi / 9))) ** 2 = sin(-2*pi/9)**2/(4*sin(-pi/9)**2),
{
field_simp at *,
repeat {left},
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
have : cos(-pi/9) ** 2 = cos(-2*pi/9) / 2 + 1 / 2,
{
have : cos(-2*pi/9) = cos(2*(-pi/9)),
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


lemma Trigo_number_generalization_step1_838 : cos(911*pi/3)=4 * cos(-pi/9) ** 3 - 3 * cos(-pi/9):=
begin
have : cos(-pi/3) = cos(911*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (152),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_number_generalization_step1_839 : cos(5*pi/4)=cos(-pi)*cos(pi/4) + (sin(pi/8)*cos(-pi/8) - sin(-pi/8)*cos(pi/8))*sin(-pi):=
begin
have : (sin(pi / 8) * cos(-pi / 8) - sin(-pi / 8) * cos(pi / 8)) * sin(-pi) + cos(pi / 4) * cos(-pi) = cos(-pi)*cos(pi/4) + (sin(pi/8)*cos(-pi/8) - sin(-pi/8)*cos(pi/8))*sin(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/4) = sin(pi/8) * cos(-pi/8) - sin(-pi/8) * cos(pi/8),
{
have : sin(pi/4) = sin((pi/8) - (-pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/4) = sin(pi/4) * sin(-pi) + cos(pi/4) * cos(-pi),
{
have : cos(5*pi/4) = cos((pi/4) - (-pi)),
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


lemma Trigo_number_generalization_step1_840 (h0 : cos(-pi/4)≠ 0) (h1 : (4*cos(-pi/4)**2)≠ 0) (h2 : (2*cos(-pi/4))≠ 0) : cos(-pi/2)=-sin(-pi/2)**2/(4*cos(-pi/4)**2) + cos(-pi/4)**2:=
begin
have : -(sin(-pi / 2) / (2 * cos(-pi / 4))) ** 2 + cos(-pi / 4) ** 2 = -sin(-pi/2)**2/(4*cos(-pi/4)**2) + cos(-pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/4) = sin(-pi/2) / ( 2 * cos(-pi/4) ),
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


lemma Trigo_number_generalization_step1_841 : cos(-pi/2)=cos(-pi)*cos(pi/2) - (sin(pi/9)*cos(7*pi/18) + sin(7*pi/18)*cos(pi/9))*sin(-pi):=
begin
have : -sin(-pi) * (sin(7 * pi / 18) * cos(pi / 9) + sin(pi / 9) * cos(7 * pi / 18)) + cos(-pi) * cos(pi / 2) = cos(-pi)*cos(pi/2) - (sin(pi/9)*cos(7*pi/18) + sin(7*pi/18)*cos(pi/9))*sin(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(7*pi/18) * cos(pi/9) + sin(pi/9) * cos(7*pi/18),
{
have : sin(pi/2) = sin((7*pi/18) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = - sin(-pi) * sin(pi/2) + cos(-pi) * cos(pi/2),
{
have : cos(-pi/2) = cos((-pi) + (pi/2)),
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


lemma Trigo_number_generalization_step1_842 : 2*sin(-pi/2)*cos(-pi/2)=- sin(504*pi):=
begin
have : sin(-pi / 2) * cos(-pi / 2) + sin(-pi / 2) * cos(-pi / 2) = 2*sin(-pi/2)*cos(-pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(-pi/2) * cos(-pi/2) + sin(-pi/2) * cos(-pi/2),
{
have : sin(-pi) = sin((-pi/2) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(504*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (252),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_843 : 2*sin(-3*pi/4)*cos(-3*pi/4)=- 4 * sin(-pi/2) ** 3 + 3 * sin(-pi/2):=
begin
have : 2 * sin((-3) * pi / 4) * cos((-3) * pi / 4) = 2*sin(-3*pi/4)*cos(-3*pi/4),
{
field_simp at *,
},
have : sin(-3*pi/2) = 2 * sin(-3*pi/4) * cos(-3*pi/4),
{
have : sin(-3*pi/2) = sin(2*(-3*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
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


lemma Trigo_number_generalization_step1_844 : -3*cos(pi/12) + 4*cos(pi/12)**3=cos(2687*pi/4):=
begin
have : 4 * cos(pi / 12) ** 3 - 3 * cos(pi / 12) = -3*cos(pi/12) + 4*cos(pi/12)**3,
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
have : cos(pi/4) = cos(2687*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/4) (336),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_845 : -cos(2239*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = -cos(2239*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (186),
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


lemma Trigo_number_generalization_step1_846 : -tan(2672*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = -tan(2672*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (891),
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


lemma Trigo_number_generalization_step1_847 : -sin(9383*pi/6)=1 / 2:=
begin
have : sin(5*pi/6) = -sin(9383*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/6) (781),
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


lemma Trigo_number_generalization_step1_848 : sin(-79*pi/120)*cos(-pi/3) - sin(-pi/3)*cos(-79*pi/120)=sin(-pi/5) * cos(pi/8) - sin(pi/8) * cos(-pi/5):=
begin
have : sin((-79) * pi / 120) * cos(-pi / 3) - sin(-pi / 3) * cos((-79) * pi / 120) = sin(-79*pi/120)*cos(-pi/3) - sin(-pi/3)*cos(-79*pi/120),
{
field_simp at *,
},
have : sin(-13*pi/40) = sin(-79*pi/120) * cos(-pi/3) - sin(-pi/3) * cos(-79*pi/120),
{
have : sin(-13*pi/40) = sin((-79*pi/120) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-13*pi/40) = sin(-pi/5) * cos(pi/8) - sin(pi/8) * cos(-pi/5),
{
have : sin(-13*pi/40) = sin((-pi/5) - (pi/8)),
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


lemma Trigo_number_generalization_step1_849 : cos(1269*pi/2)**2=1 / 2 - cos(-2*pi) / 2:=
begin
have : (-cos(1269 * pi / 2)) ** 2 = cos(1269*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(1269*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (316),
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


lemma Trigo_number_generalization_step1_850 : sin(pi/7) / cos(pi/7)=-tan(6796*pi/7):=
begin
have : tan(pi/7) = -tan(6796*pi/7),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/7) (971),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/7) / cos(pi/7) = tan(pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_851 : tan(1168*pi/7)=sin(-pi/7) / cos(-pi/7):=
begin
have : tan(-pi/7) = tan(1168*pi/7),
{
rw tan_eq_tan_add_int_mul_pi (-pi/7) (167),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/7) = sin(-pi/7) / cos(-pi/7),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_852 : -cos(1083*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(1083*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (135),
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


lemma Trigo_number_generalization_step1_853 : sin(236*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = sin(236*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (39),
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


lemma Trigo_number_generalization_step1_854 : sin(pi/8)*sin(539*pi)=sin(5*pi/8) / 2 + sin(-3*pi/8) / 2:=
begin
have : cos(-pi/2) = sin(539*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (269),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) * cos(-pi/2) = sin(5*pi/8) / 2 + sin(-3*pi/8) / 2,
{
rw sin_mul_cos,
have : sin((pi/8) + (-pi/2)) = sin(-3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/8) - (-pi/2)) = sin(5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_855 : -cos(2080*pi/3)=cos(5801*pi/3):=
begin
have : cos(-pi/3) = -cos(2080*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (346),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(5801*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (967),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_856 : -sin(291*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = -sin(291*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (36),
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


lemma Trigo_number_generalization_step1_857 : cos(4813*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = cos(4813*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (3*pi/4) (602),
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


lemma Trigo_number_generalization_step1_858 : sin(9505*pi/9)=sin(11204*pi/9):=
begin
have : sin(pi/9) = sin(9505*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/9) (528),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(11204*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (622),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_859 : -sin(35807*pi/18)=2 * cos(pi/9) ** 2 - 1:=
begin
have : cos(2*pi/9) = -sin(35807*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/9) (994),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = 2 * cos(pi/9) ** 2 - 1,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_860 : -sin(6757*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -sin(6757*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (3*pi/4) (845),
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


lemma Trigo_number_generalization_step1_861 : -cos(569*pi/8)=cos(6383*pi/8):=
begin
have : cos(-pi/8) = -cos(569*pi/8),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/8) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/8) = cos(6383*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/8) (399),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_862 : cos(-pi/6)=-cos(4685*pi/6):=
begin
have : sin(3479*pi/3) = cos(4685*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3479*pi/3) (970),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(3479*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (579),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_863 : -cos(2515*pi/14)=- sin(12727*pi/7):=
begin
have : sin(-pi/7) = -cos(2515*pi/14),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/7) = - sin(12727*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/7) (909),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_864 : -sin(3247*pi/3)=- sqrt( 3 ) / 2:=
begin
have : cos(5*pi/6) = -sin(3247*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (540),
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


lemma Trigo_number_generalization_step1_865 : -cos(5428*pi/9)=cos(12797*pi/9):=
begin
have : cos(pi/9) = -cos(5428*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/9) (301),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = cos(12797*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (711),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_866 : -sin(pi/7)*sin(13*pi/7) + cos(pi/7)*cos(13*pi/7)=- cos(531*pi):=
begin
have : -sin(13 * pi / 7) * sin(pi / 7) + cos(13 * pi / 7) * cos(pi / 7) = -sin(pi/7)*sin(13*pi/7) + cos(pi/7)*cos(13*pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(13*pi/7) * sin(pi/7) + cos(13*pi/7) * cos(pi/7),
{
have : cos(2*pi) = cos((13*pi/7) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - cos(531*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (264),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_867 : sin(-pi/4)*cos(-pi/3) - sin(-pi/3)*cos(-pi/4)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = sin(-pi/4) * cos(-pi/3) - sin(-pi/3) * cos(-pi/4),
{
have : sin(pi/12) = sin((-pi/4) - (-pi/3)),
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


lemma Trigo_number_generalization_step1_868 : -sin(pi/4)**2 + cos(pi/4)**2=cos(2511*pi/2):=
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
have : cos(pi/2) = cos(2511*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (628),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_869 : -cos(pi/5) - sin(3563*pi/2)=- 2 * sin(-11*pi/10) * sin(-9*pi/10):=
begin
have : -sin(3563 * pi / 2) - cos(pi / 5) = -cos(pi/5) - sin(3563*pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(3563*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (891),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) - cos(pi/5) = - 2 * sin(-11*pi/10) * sin(-9*pi/10),
{
rw cos_sub_cos,
have : sin(((-2*pi) + (pi/5))/2) = sin(-9*pi/10),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-2*pi) - (pi/5))/2) = sin(-11*pi/10),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_870 : sin(pi/2) * sin(pi/8)=sin(pi/8)*sin(pi/2):=
begin
have : (-1) / 2 * ((-2) * sin(pi / 8) * sin(pi / 2)) = sin(pi/8)*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/8) - cos(3*pi/8) = -2 * sin(pi/8) * sin(pi/2),
{
rw cos_sub_cos,
have : sin(((5*pi/8) + (3*pi/8))/2) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((5*pi/8) - (3*pi/8))/2) = sin(pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : -1/2*(cos(5*pi/8) - cos(3*pi/8)) = cos(3*pi/8)/2-cos(5*pi/8)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/2) * sin(pi/8) = cos(3*pi/8) / 2 - cos(5*pi/8) / 2,
{
rw sin_mul_sin,
have : cos((pi/2) + (pi/8)) = cos(5*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (pi/8)) = cos(3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_871 : -sin(-pi/4)*sin(1064*pi/5)=cos(-pi/20) / 2 - cos(-9*pi/20) / 2:=
begin
have : sin(-pi / 4) * -sin(1064 * pi / 5) = -sin(-pi/4)*sin(1064*pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/5) = -sin(1064*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/5) (106),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) * sin(-pi/5) = cos(-pi/20) / 2 - cos(-9*pi/20) / 2,
{
rw sin_mul_sin,
have : cos((-pi/4) + (-pi/5)) = cos(-9*pi/20),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/4) - (-pi/5)) = cos(-pi/20),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_872 : sin(-pi)*cos(454*pi/3)=cos(5*pi/6) / 2 - cos(-7*pi/6) / 2:=
begin
have : cos(454 * pi / 3) * sin(-pi) = sin(-pi)*cos(454*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(454*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * sin(-pi) = cos(5*pi/6) / 2 - cos(-7*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((-pi/6) + (-pi)) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (-pi)) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_873 : -cos(5109*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = -cos(5109*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (638),
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


lemma Trigo_number_generalization_step1_874 : -cos(2654*pi/3)=1 / 2:=
begin
have : sin(pi/6) = -cos(2654*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (442),
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


lemma Trigo_number_generalization_step1_875 : sin(pi)=2*(cos(-pi/9)*cos(11*pi/18) - sin(-pi/9)*sin(11*pi/18))*sin(pi/2):=
begin
have : 2 * sin(pi / 2) * (-sin(11 * pi / 18) * sin(-pi / 9) + cos(11 * pi / 18) * cos(-pi / 9)) = 2*(cos(-pi/9)*cos(11*pi/18) - sin(-pi/9)*sin(11*pi/18))*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -sin(11*pi/18) * sin(-pi/9) + cos(11*pi/18) * cos(-pi/9),
{
have : cos(pi/2) = cos((11*pi/18) + (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_876 : cos(3821*pi/2) + sin(-pi)=2 * sin(-3*pi/2) * cos(-pi/2):=
begin
have : sin(-2*pi) = cos(3821*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (954),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) + sin(-pi) = 2 * sin(-3*pi/2) * cos(-pi/2),
{
rw sin_add_sin,
have : sin(((-2*pi) + (-pi))/2) = sin(-3*pi/2),
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
},
rw this,
end


lemma Trigo_number_generalization_step1_877 (h0 : tan(7931*pi/8)≠ 0) : -1/tan(7931*pi/8)=- tan(4017*pi/8):=
begin
have : (-1) / tan(7931 * pi / 8) = -1/tan(7931*pi/8),
{
field_simp at *,
},
have : tan(-pi/8) = -1 / tan(7931*pi/8),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/8) (991),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/8) = - tan(4017*pi/8),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/8) (502),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_878 : 2*sin(-3*pi/7)*cos(4*pi/7)=2 * sin(-3*pi/7) * cos(-4*pi/7):=
begin
have : 2 * sin((-3) * pi / 7) * cos(4 * pi / 7) = 2*sin(-3*pi/7)*cos(4*pi/7),
{
field_simp at *,
},
have : sin(pi/7) + sin(-pi) = 2 * sin(-3*pi/7) * cos(4*pi/7),
{
rw sin_add_sin,
have : sin(((pi/7) + (-pi))/2) = sin(-3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/7) - (-pi))/2) = cos(4*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/7) + sin(-pi)) = sin(-pi)+sin(pi/7),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(-pi) + sin(pi/7) = 2 * sin(-3*pi/7) * cos(-4*pi/7),
{
rw sin_add_sin,
have : sin(((-pi) + (pi/7))/2) = sin(-3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (pi/7))/2) = cos(-4*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_879 : cos(-pi/5)=-3*sin(18913*pi/30) + 4*sin(18913*pi/30)**3:=
begin
have : -((-4) * sin(18913 * pi / 30) ** 3 + 3 * sin(18913 * pi / 30)) = -3*sin(18913*pi/30) + 4*sin(18913*pi/30)**3,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(18913*pi/10) = -4 * sin(18913*pi/30) ** 3 + 3 * sin(18913*pi/30),
{
have : sin(18913*pi/10) = sin(3*(18913*pi/30)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) = - sin(18913*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/5) (945),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_880 : sin(-pi/8) * sin(pi/8)=-cos(0)/2 + sin(7979*pi/4)/2:=
begin
have : sin(7979 * pi / 4) / 2 - cos(0) / 2 = -cos(0)/2 + sin(7979*pi/4)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = sin(7979*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/4) (997),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/8) * sin(pi/8) = cos(-pi/4) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
have : cos((-pi/8) + (pi/8)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/8) - (pi/8)) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_881 (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) : sin(-2*pi)/cos(-2*pi)=1 / tan(261*pi/2):=
begin
have : sin((-2) * pi) / cos((-2) * pi) = sin(-2*pi)/cos(-2*pi),
{
field_simp at *,
},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = 1 / tan(261*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-2*pi) (128),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_882 : -cos(23315*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(23315*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (971),
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


lemma Trigo_number_generalization_step1_883 : sin(pi/12)*cos(-pi/6) - sin(-pi/6)*cos(pi/12)=cos(2607*pi/4):=
begin
have : sin(pi/4) = sin(pi/12) * cos(-pi/6) - sin(-pi/6) * cos(pi/12),
{
have : sin(pi/4) = sin((pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(2607*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (325),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_884 : cos(632*pi)=- sin(1575*pi/2):=
begin
have : cos(2*pi) = cos(632*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (315),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - sin(1575*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (394),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_885 : cos(183*pi)=- 1:=
begin
have : cos(pi) = cos(183*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (92),
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


lemma Trigo_number_generalization_step1_886 : -cos(1330*pi/3)=1 / 2:=
begin
have : sin(5*pi/6) = -cos(1330*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (221),
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


lemma Trigo_number_generalization_step1_887 : cos(2463*pi/2)=- cos(1053*pi/2):=
begin
have : sin(-pi) = cos(2463*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (615),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - cos(1053*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (262),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_888 : sin(pi) ** 2=-cos(pi/7)*cos(13*pi/7)/2 + sin(pi/7)*sin(13*pi/7)/2 + 1/2:=
begin
have : 1 / 2 - (-sin(13 * pi / 7) * sin(pi / 7) + cos(13 * pi / 7) * cos(pi / 7)) / 2 = -cos(pi/7)*cos(13*pi/7)/2 + sin(pi/7)*sin(13*pi/7)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -sin(13*pi/7) * sin(pi/7) + cos(13*pi/7) * cos(pi/7),
{
have : cos(2*pi) = cos((13*pi/7) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) ** 2 = 1 / 2 - cos(2*pi) / 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_889 : -sin(pi)**2 + cos(pi)**2=1 - 2 * sin(pi) ** 2:=
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


lemma Trigo_number_generalization_step1_890 : -sin(6035*pi/4) + sin(-pi/9)=2 * sin(-13*pi/72) * cos(5*pi/72):=
begin
have : sin(-pi / 9) - sin(6035 * pi / 4) = -sin(6035*pi/4) + sin(-pi/9),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(6035*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (754),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) - sin(pi/4) = 2 * sin(-13*pi/72) * cos(5*pi/72),
{
rw sin_sub_sin,
have : cos(((-pi/9) + (pi/4))/2) = cos(5*pi/72),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/9) - (pi/4))/2) = sin(-13*pi/72),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_891 : cos(7701*pi/4)=- sin(-pi/2) * sin(-pi/4) + cos(-pi/2) * cos(-pi/4):=
begin
have : cos(-3*pi/4) = cos(7701*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (-3*pi/4) (963),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/4) = - sin(-pi/2) * sin(-pi/4) + cos(-pi/2) * cos(-pi/4),
{
have : cos(-3*pi/4) = cos((-pi/2) + (-pi/4)),
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


lemma Trigo_number_generalization_step1_892 : sin(8327*pi/6)=- sin(11501*pi/6):=
begin
have : sin(-pi/6) = sin(8327*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (694),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(11501*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (958),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_893 (h0 : tan(398*pi/3)≠ 0) : -1/tan(398*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(398 * pi / 3) = -1/tan(398*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(398*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (132),
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


lemma Trigo_number_generalization_step1_894 : sin(-13*pi/36)*sin(-pi/9) + cos(-13*pi/36)*cos(-pi/9)=- cos(7141*pi/4):=
begin
have : sin((-13) * pi / 36) * sin(-pi / 9) + cos((-13) * pi / 36) * cos(-pi / 9) = sin(-13*pi/36)*sin(-pi/9) + cos(-13*pi/36)*cos(-pi/9),
{
field_simp at *,
},
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
have : cos(-pi/4) = - cos(7141*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/4) (892),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_895 : sin(1502*pi/9)**2=1 / 2 - cos(-2*pi/9) / 2:=
begin
have : (-sin(1502 * pi / 9)) ** 2 = sin(1502*pi/9)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = -sin(1502*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/9) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_number_generalization_step1_896 : -sin(5161*pi/4)=4 * cos(pi/4) ** 3 - 3 * cos(pi/4):=
begin
have : cos(3*pi/4) = -sin(5161*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (644),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_number_generalization_step1_897 : cos(-pi/5) ** 2=1 - (sin(-11*pi/5)*cos(-2*pi) - sin(-2*pi)*cos(-11*pi/5))**2:=
begin
have : 1 - (sin((-11) * pi / 5) * cos((-2) * pi) - sin((-2) * pi) * cos((-11) * pi / 5)) ** 2 = 1 - (sin(-11*pi/5)*cos(-2*pi) - sin(-2*pi)*cos(-11*pi/5))**2,
{
field_simp at *,
},
have : sin(-pi/5) = sin(-11*pi/5) * cos(-2*pi) - sin(-2*pi) * cos(-11*pi/5),
{
have : sin(-pi/5) = sin((-11*pi/5) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/5) ** 2 = 1 - sin(-pi/5) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_898 : sin(1333*pi/2)=- sin(2659*pi/2):=
begin
have : sin(pi/2) = sin(1333*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (333),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(2659*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (664),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_899 : -sin(pi/4)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/4)=1 / 2:=
begin
have : sin(5 * pi / 12) * cos(pi / 4) - sin(pi / 4) * cos(5 * pi / 12) = -sin(pi/4)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(5*pi/12) * cos(pi/4) - sin(pi/4) * cos(5*pi/12),
{
have : sin(pi/6) = sin((5*pi/12) - (pi/4)),
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


lemma Trigo_number_generalization_step1_900 : -sin(4739*pi/4)=cos(7733*pi/4):=
begin
have : sin(-pi/4) = -sin(4739*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (592),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = cos(7733*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (966),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_901 : sin(-pi/2)=2*(cos(-7*pi/12)*cos(-pi/3) + sin(-7*pi/12)*sin(-pi/3))*sin(-pi/4):=
begin
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


lemma Trigo_number_generalization_step1_902 : -sin(3781*pi/2)=- 1:=
begin
have : cos(pi) = -sin(3781*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (945),
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


lemma Trigo_number_generalization_step1_903 : cos(9035*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = cos(9035*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (753),
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


lemma Trigo_number_generalization_step1_904 : cos(1398*pi)=1:=
begin
have : sin(pi/2) = cos(1398*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (699),
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


lemma Trigo_number_generalization_step1_905 : cos(1470*pi)=1:=
begin
have : sin(pi/2) = cos(1470*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (735),
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


lemma Trigo_number_generalization_step1_906 : -sin(1892*pi)=- cos(943*pi/2):=
begin
have : sin(2*pi) = -sin(1892*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (947),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(943*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (236),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_907 : tan(93*pi/2)=- 1 / tan(225*pi):=
begin
have : tan(pi/2) = tan(93*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - 1 / tan(225*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/2) (224),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_908 (h0 : tan(2513*pi/6)≠ 0) : 1/tan(2513*pi/6)=- sqrt( 3 ):=
begin
have : tan(2*pi/3) = 1 / tan(2513*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/3) (419),
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


lemma Trigo_number_generalization_step1_909 : sin(5111*pi/6)**2=1 - sin(pi/3) ** 2:=
begin
have : (-sin(5111 * pi / 6)) ** 2 = sin(5111*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(5111*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (425),
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


lemma Trigo_number_generalization_step1_910 : sin(-pi/3) + sin(-pi/7)=2*(-1 + 2*cos(-pi/21)**2)*sin(-5*pi/21):=
begin
have : 2 * sin((-5) * pi / 21) * (2 * cos(-pi / 21) ** 2 - 1) = 2*(-1 + 2*cos(-pi/21)**2)*sin(-5*pi/21),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/21) = 2 * cos(-pi/21) ** 2 - 1,
{
have : cos(-2*pi/21) = cos(2*(-pi/21)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) + sin(-pi/7) = 2 * sin(-5*pi/21) * cos(-2*pi/21),
{
rw sin_add_sin,
have : sin(((-pi/3) + (-pi/7))/2) = sin(-5*pi/21),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (-pi/7))/2) = cos(-2*pi/21),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_911 : sin(1827*pi)**2=1 / 2 - cos(2*pi) / 2:=
begin
have : sin(pi) = sin(1827*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (913),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) ** 2 = 1 / 2 - cos(2*pi) / 2,
{
have : cos(2*pi) = cos(2*(pi)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_912 : cos(-pi/3) ** 2=cos(-2*pi/3)/2 + 1/2:=
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


lemma Trigo_number_generalization_step1_913 : sin(13541*pi/8)=- sin(12397*pi/8):=
begin
have : cos(pi/8) = sin(13541*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/8) (846),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = - sin(12397*pi/8),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (774),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_914 (h0 : tan(2951*pi/3)≠ 0) : -1/tan(2951*pi/3)=sqrt( 3 ) / 3:=
begin
have : (-1) / tan(2951 * pi / 3) = -1/tan(2951*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(2951*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (983),
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


lemma Trigo_number_generalization_step1_915 (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : sin(pi/3)/(2*cos(pi/6))=1 / 2:=
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
have : sin(pi/6) = 1 / 2,
{
rw sin_pi_div_six,
},
rw this,
end


lemma Trigo_number_generalization_step1_916 : -cos(462*pi)=sin(3651*pi/2):=
begin
have : cos(pi) = -cos(462*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (231),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(3651*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (912),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_917 (h0 : cos((2*pi/7)/2)≠ 0) (h1 : (cos(2*pi/7)+1)≠ 0) (h2 : (1+cos(2*pi/7))≠ 0) : sin(2*pi/7)/(cos(2*pi/7) + 1)=- tan(5816*pi/7):=
begin
have : sin(2 * pi / 7) / (1 + cos(2 * pi / 7)) = sin(2*pi/7)/(cos(2*pi/7) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/7) = sin(2*pi/7) / ( 1 + cos(2*pi/7) ),
{
have : tan(pi/7) = tan((2*pi/7)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/7) = - tan(5816*pi/7),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/7) (831),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_918 : sin(5179*pi/4)=- cos(261*pi/4):=
begin
have : cos(pi/4) = sin(5179*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/4) (647),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = - cos(261*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_919 : sin(359*pi/4)=- sin(6465*pi/4):=
begin
have : sin(-pi/4) = sin(359*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/4) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = - sin(6465*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (808),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_920 (h0 : tan(8263*pi/12)≠ 0) : -1/tan(8263*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / tan(8263 * pi / 12) = -1/tan(8263*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(8263*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (688),
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


lemma Trigo_number_generalization_step1_921 : -sin(pi/8)*sin(5*pi/24) + cos(pi/8)*cos(5*pi/24)=1 / 2:=
begin
have : -sin(5 * pi / 24) * sin(pi / 8) + cos(5 * pi / 24) * cos(pi / 8) = -sin(pi/8)*sin(5*pi/24) + cos(pi/8)*cos(5*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(5*pi/24) * sin(pi/8) + cos(5*pi/24) * cos(pi/8),
{
have : cos(pi/3) = cos((5*pi/24) + (pi/8)),
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


lemma Trigo_number_generalization_step1_923 : 2*sin(-pi/16)*cos(-pi/16)=- cos(13459*pi/8):=
begin
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
have : sin(-pi/8) = - cos(13459*pi/8),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/8) (841),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_924 : -3*cos(pi/12) + 4*cos(pi/12)**3=sqrt( 2 ) / 2:=
begin
have : 4 * cos(pi / 12) ** 3 - 3 * cos(pi / 12) = -3*cos(pi/12) + 4*cos(pi/12)**3,
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_925 : tan(2353*pi/3)=sqrt( 3 ):=
begin
have : tan(pi/3) = tan(2353*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (784),
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


lemma Trigo_number_generalization_step1_926 : sin(10212*pi/7)=sin(7006*pi/7):=
begin
have : sin(pi/7) = sin(10212*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/7) (729),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = sin(7006*pi/7),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/7) (500),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_927 : cos(6609*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi/4) = cos(6609*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (826),
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


lemma Trigo_number_generalization_step1_928 (h0 : sin(4*pi)≠ 0) (h1 : (2*sin(4*pi))≠ 0) : sin(8*pi)/(2*sin(4*pi))=- sin(2*pi) ** 2 + cos(2*pi) ** 2:=
begin
have : cos(4*pi) = sin(8*pi) / ( 2 * sin(4*pi) ),
{
have : sin(8*pi) = sin(2*(4*pi)),
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


lemma Trigo_number_generalization_step1_929 : -sin(6146*pi/5)=sin(4144*pi/5):=
begin
have : sin(pi/5) = -sin(6146*pi/5),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/5) (614),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = sin(4144*pi/5),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/5) (414),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_930 : 2*sin(pi/18)*cos(pi/18)=- sin(6011*pi/9):=
begin
have : sin(pi/9) = 2 * sin(pi/18) * cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = - sin(6011*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/9) (334),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_931 : -sin(pi/24)*sin(pi/8) + cos(pi/24)*cos(pi/8)=sqrt( 3 ) / 2:=
begin
have : cos(pi/6) = -sin(pi/24) * sin(pi/8) + cos(pi/24) * cos(pi/8),
{
have : cos(pi/6) = cos((pi/24) + (pi/8)),
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


lemma Trigo_number_generalization_step1_932 (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) : sin(-2*pi)/cos(-2*pi)=tan(708*pi):=
begin
have : sin((-2) * pi) / cos((-2) * pi) = sin(-2*pi)/cos(-2*pi),
{
field_simp at *,
},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = tan(708*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (710),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_933 : (-4*sin(pi/21)**3 + 3*sin(pi/21))*cos(pi/5)=- sin(2*pi/35) / 2 + sin(12*pi/35) / 2:=
begin
have : ((-4) * sin(pi / 21) ** 3 + 3 * sin(pi / 21)) * cos(pi / 5) = (-4*sin(pi/21)**3 + 3*sin(pi/21))*cos(pi/5),
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
have : sin(pi/7) * cos(pi/5) = - sin(2*pi/35) / 2 + sin(12*pi/35) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/5) + (pi/7)) = sin(12*pi/35),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (pi/7)) = sin(2*pi/35),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_934 : sin(-13*pi/42)*cos(pi/7) + sin(pi/7)*cos(-13*pi/42)=sin(7579*pi/6):=
begin
have : sin((-13) * pi / 42) * cos(pi / 7) + sin(pi / 7) * cos((-13) * pi / 42) = sin(-13*pi/42)*cos(pi/7) + sin(pi/7)*cos(-13*pi/42),
{
field_simp at *,
},
have : sin(-pi/6) = sin(-13*pi/42) * cos(pi/7) + sin(pi/7) * cos(-13*pi/42),
{
have : sin(-pi/6) = sin((-13*pi/42) + (pi/7)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(7579*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (631),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_935 : -sin(pi/18)**2 + cos(pi/18)**2=- cos(5678*pi/9):=
begin
have : cos(pi/9) = -sin(pi/18) ** 2 + cos(pi/18) ** 2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = - cos(5678*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/9) (315),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_936 : sin(5745*pi/8)**2 + cos(pi/8)**2=1:=
begin
have : sin(pi/8) = sin(5745*pi/8),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/8) (359),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) ** 2 + cos(pi/8) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_number_generalization_step1_937 : cos(13*pi/40)=-sin(pi/8)*sin(pi/5) + cos(13*pi/40)/2 + cos(-3*pi/40)/2:=
begin
have : -sin(pi / 8) * sin(pi / 5) + (cos((-3) * pi / 40) / 2 + cos(13 * pi / 40) / 2) = -sin(pi/8)*sin(pi/5) + cos(13*pi/40)/2 + cos(-3*pi/40)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) * cos(pi/5) = cos(-3*pi/40) / 2 + cos(13*pi/40) / 2,
{
rw cos_mul_cos,
have : cos((pi/8) + (pi/5)) = cos(13*pi/40),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/8) - (pi/5)) = cos(-3*pi/40),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (cos(pi/8) * cos(pi/5)) = cos(pi/8)*cos(pi/5),
{
ring,
},
have : cos(13*pi/40) = - sin(pi/8) * sin(pi/5) + cos(pi/8) * cos(pi/5),
{
have : cos(13*pi/40) = cos((pi/8) + (pi/5)),
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


lemma Trigo_number_generalization_step1_938 : cos(-pi/4)*cos(7*pi/4) + sin(-pi/4)*sin(7*pi/4)=1 - 2 * sin(pi) ** 2:=
begin
have : sin(7 * pi / 4) * sin(-pi / 4) + cos(7 * pi / 4) * cos(-pi / 4) = cos(-pi/4)*cos(7*pi/4) + sin(-pi/4)*sin(7*pi/4),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(7*pi/4) * sin(-pi/4) + cos(7*pi/4) * cos(-pi/4),
{
have : cos(2*pi) = cos((7*pi/4) - (-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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
rw this,
end


lemma Trigo_number_generalization_step1_939 : -4*sin(pi/9)**3 + 3*sin(pi/9)=- sin(5585*pi/3):=
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
have : sin(pi/3) = - sin(5585*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (931),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_940 : -cos(2534*pi/3)=1 / 2:=
begin
have : sin(5*pi/6) = -cos(2534*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (422),
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


lemma Trigo_number_generalization_step1_941 : -cos(19673*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/12) = -cos(19673*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (819),
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


lemma Trigo_number_generalization_step1_942 : -sin(754*pi/3)=sin(1387*pi/3):=
begin
have : sin(pi/3) = -sin(754*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (125),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(1387*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (231),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_943 : sin(-pi/9)*sin(2*pi/63) + cos(-pi/9)*cos(2*pi/63)=cos(1441*pi/7):=
begin
have : sin(2 * pi / 63) * sin(-pi / 9) + cos(2 * pi / 63) * cos(-pi / 9) = sin(-pi/9)*sin(2*pi/63) + cos(-pi/9)*cos(2*pi/63),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = sin(2*pi/63) * sin(-pi/9) + cos(2*pi/63) * cos(-pi/9),
{
have : cos(pi/7) = cos((2*pi/63) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = cos(1441*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/7) (103),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_944 : -sin(18489*pi/10)=4 * cos(-pi/5) ** 3 - 3 * cos(-pi/5):=
begin
have : cos(-3*pi/5) = -sin(18489*pi/10),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/5) (924),
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


lemma Trigo_number_generalization_step1_945 (h0 : tan(1951*pi/2)≠ 0) : sin(pi) / cos(pi)=-1/tan(1951*pi/2):=
begin
have : (-1) / tan(1951 * pi / 2) = -1/tan(1951*pi/2),
{
field_simp at *,
},
have : tan(pi) = -1 / tan(1951*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (974),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) / cos(pi) = tan(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_946 : -sin(588*pi)=cos(2713*pi/2):=
begin
have : cos(pi/2) = -sin(588*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (293),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(2713*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (678),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_947 (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : sin(pi/8) + sin(2*pi/3)/(2*cos(pi/3))=2 * sin(11*pi/48) * cos(-5*pi/48):=
begin
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
have : sin(pi/8) + sin(pi/3) = 2 * sin(11*pi/48) * cos(-5*pi/48),
{
rw sin_add_sin,
have : sin(((pi/8) + (pi/3))/2) = sin(11*pi/48),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/8) - (pi/3))/2) = cos(-5*pi/48),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_948 : sin(-pi)=cos(4619*pi/2):=
begin
have : cos(3251*pi/2) = cos(4619*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (3251*pi/2) (342),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(3251*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (812),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_949 : cos(1189*pi/6)=- cos(3293*pi/6):=
begin
have : cos(-pi/6) = cos(1189*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(3293*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (274),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_950 : (-1 + 2*cos(pi/16)**2)*cos(2*pi)=cos(15*pi/8) / 2 + cos(17*pi/8) / 2:=
begin
have : cos(2 * pi) * (2 * cos(pi / 16) ** 2 - 1) = (-1 + 2*cos(pi/16)**2)*cos(2*pi),
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
have : cos(2*pi) * cos(pi/8) = cos(15*pi/8) / 2 + cos(17*pi/8) / 2,
{
rw cos_mul_cos,
have : cos((2*pi) + (pi/8)) = cos(17*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (pi/8)) = cos(15*pi/8),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_951 : -sin(1643*pi/14)=sin(17953*pi/14):=
begin
have : cos(pi/7) = -sin(1643*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/7) = sin(17953*pi/14),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/7) (641),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_952 (h0 : sin(2607*pi/4)≠ 0) (h1 : (2*sin(2607*pi/4))≠ 0) : sin(-pi/4)=-sin(2607*pi/2)/(2*sin(2607*pi/4)):=
begin
have : -(sin(2607 * pi / 2) / (2 * sin(2607 * pi / 4))) = -sin(2607*pi/2)/(2*sin(2607*pi/4)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2607*pi/4) = sin(2607*pi/2) / ( 2 * sin(2607*pi/4) ),
{
have : sin(2607*pi/2) = sin(2*(2607*pi/4)),
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
have : sin(-pi/4) = - cos(2607*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (325),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_953 : cos(3183*pi/4)=- sin(2223*pi/4):=
begin
have : cos(-pi/4) = cos(3183*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/4) (398),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = - sin(2223*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (277),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_954 : -sin(pi/6)*sin(pi/2) + cos(pi/6)*cos(pi/2)=- 1 / 2:=
begin
have : cos(2*pi/3) = -sin(pi/6) * sin(pi/2) + cos(pi/6) * cos(pi/2),
{
have : cos(2*pi/3) = cos((pi/6) + (pi/2)),
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


lemma Trigo_number_generalization_step1_955 : -sin(-pi/4)*sin(5065*pi/8)=cos(-3*pi/8) / 2 - cos(-pi/8) / 2:=
begin
have : sin(-pi / 4) * -sin(5065 * pi / 8) = -sin(-pi/4)*sin(5065*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -sin(5065*pi/8),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/8) (316),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_number_generalization_step1_956 (h0 : tan(1259*pi/2)≠ 0) : 1/tan(1259*pi/2)=0:=
begin
have : tan(pi) = 1 / tan(1259*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (630),
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


lemma Trigo_number_generalization_step1_957 : cos(2333*pi/3)**2 + sin(pi/3)**2=1:=
begin
have : sin(pi / 3) ** 2 + cos(2333 * pi / 3) ** 2 = cos(2333*pi/3)**2 + sin(pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(2333*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (389),
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


lemma Trigo_number_generalization_step1_958 : -cos(1375*pi/2)=- 4 * sin(-2*pi) ** 3 + 3 * sin(-2*pi):=
begin
have : sin(-6*pi) = -cos(1375*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-6*pi) (340),
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


lemma Trigo_number_generalization_step1_959 : cos(77*pi/2)**2=cos(-pi) / 2 + 1 / 2:=
begin
have : cos(-pi/2) = cos(77*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) ** 2 = cos(-pi) / 2 + 1 / 2,
{
have : cos(-pi) = cos(2*(-pi/2)),
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


lemma Trigo_number_generalization_step1_960 : sin(-2*pi) * sin(pi/5)=2*cos(-11*pi/15)**3 - cos(-9*pi/5)/2 - 3*cos(-11*pi/15)/2:=
begin
have : (4 * cos((-11) * pi / 15) ** 3 - 3 * cos((-11) * pi / 15)) / 2 - cos((-9) * pi / 5) / 2 = 2*cos(-11*pi/15)**3 - cos(-9*pi/5)/2 - 3*cos(-11*pi/15)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-11*pi/5) = 4 * cos(-11*pi/15) ** 3 - 3 * cos(-11*pi/15),
{
have : cos(-11*pi/5) = cos(3*(-11*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * sin(pi/5) = cos(-11*pi/5) / 2 - cos(-9*pi/5) / 2,
{
rw sin_mul_sin,
have : cos((-2*pi) + (pi/5)) = cos(-9*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/5)) = cos(-11*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_961 (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : sin(pi/3)/(2*cos(pi/6))=- cos(5320*pi/3):=
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
have : sin(pi/6) = - cos(5320*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (886),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_962 : sin(16759*pi/10)=4 * cos(pi/5) ** 3 - 3 * cos(pi/5):=
begin
have : cos(3*pi/5) = sin(16759*pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/5) (838),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/5) = 4 * cos(pi/5) ** 3 - 3 * cos(pi/5),
{
have : cos(3*pi/5) = cos(3*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
rw this,
end


lemma Trigo_number_generalization_step1_963 : -cos(21277*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(pi/12) = -cos(21277*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (886),
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


lemma Trigo_number_generalization_step1_964 : 2*sin(3*pi/8)*cos(3*pi/8)=sqrt( 2 ) / 2:=
begin
have : sin(3*pi/4) = 2 * sin(3*pi/8) * cos(3*pi/8),
{
have : sin(3*pi/4) = sin(2*(3*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sqrt( 2 ) / 2,
{
rw sin_three_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_965 : -sin(8787*pi/14)*cos(pi/7)=cos(-2*pi/7) / 2 + cos(0) / 2:=
begin
have : cos(-pi/7) = -sin(8787*pi/14),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/7) (313),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) * cos(pi/7) = cos(-2*pi/7) / 2 + cos(0) / 2,
{
rw cos_mul_cos,
have : cos((-pi/7) + (pi/7)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/7) - (pi/7)) = cos(-2*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_966 : sin(2835*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(pi/4) = sin(2835*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/4) (354),
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


lemma Trigo_number_generalization_step1_967 : sin(-11*pi/28)=sin(-pi/4)*cos(-pi/7) + (-3*cos(-pi/12) + 4*cos(-pi/12)**3)*sin(-pi/7):=
begin
have : sin(-pi / 7) * (4 * cos(-pi / 12) ** 3 - 3 * cos(-pi / 12)) + sin(-pi / 4) * cos(-pi / 7) = sin(-pi/4)*cos(-pi/7) + (-3*cos(-pi/12) + 4*cos(-pi/12)**3)*sin(-pi/7),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-11*pi/28) = sin(-pi/7) * cos(-pi/4) + sin(-pi/4) * cos(-pi/7),
{
have : sin(-11*pi/28) = sin((-pi/7) + (-pi/4)),
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


lemma Trigo_number_generalization_step1_968 : -sin(pi/8)**2 + cos(pi/8)**2=sqrt( 2 ) / 2:=
begin
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_969 : sin(1016*pi)=sin(1625*pi):=
begin
have : sin(-2*pi) = sin(1016*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (509),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(1625*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (811),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_970 : 1 - 2*sin(pi/8)**2=sqrt( 2 ) / 2:=
begin
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
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_971 : sin(pi)=cos(553*pi/2):=
begin
have : - -cos(553 * pi / 2) = cos(553*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2073*pi/2) = -cos(553*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2073*pi/2) (656),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = - cos(2073*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (518),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_972 (h0 : cos(-pi/2)≠ 0) : tan(-pi/2)=cos(27*pi)/cos(-pi/2):=
begin
have : sin(-pi/2) = cos(27*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/2) = sin(-pi/2) / cos(-pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_number_generalization_step1_973 : 1 - 2*sin(pi/6)**2=1 / 2:=
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_number_generalization_step1_974 (h0 : tan(949*pi/4)≠ 0) : 1/tan(949*pi/4)=1:=
begin
have : tan(pi/4) = 1 / tan(949*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (237),
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


lemma Trigo_number_generalization_step1_975 : -cos(-pi/5)*cos(2365*pi/2)=sin(-9*pi/5) / 2 + sin(-11*pi/5) / 2:=
begin
have : -cos(2365 * pi / 2) * cos(-pi / 5) = -cos(-pi/5)*cos(2365*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -cos(2365*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (592),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/5) = sin(-9*pi/5) / 2 + sin(-11*pi/5) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-pi/5)) = sin(-11*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-pi/5)) = sin(-9*pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_976 : (sin(-16*pi/63)*sin(-pi/9) + cos(-16*pi/63)*cos(-pi/9))*sin(2*pi)=sin(15*pi/7) / 2 + sin(13*pi/7) / 2:=
begin
have : sin(2 * pi) * (sin((-16) * pi / 63) * sin(-pi / 9) + cos((-16) * pi / 63) * cos(-pi / 9)) = (sin(-16*pi/63)*sin(-pi/9) + cos(-16*pi/63)*cos(-pi/9))*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/7) = sin(-16*pi/63) * sin(-pi/9) + cos(-16*pi/63) * cos(-pi/9),
{
have : cos(-pi/7) = cos((-16*pi/63) - (-pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(-pi/7) = sin(15*pi/7) / 2 + sin(13*pi/7) / 2,
{
rw sin_mul_cos,
have : sin((2*pi) + (-pi/7)) = sin(13*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (-pi/7)) = sin(15*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_977 : cos(-pi/9) - cos(pi/5)=-2*(sin(-29*pi/90)*cos(-pi/6) - sin(-pi/6)*cos(-29*pi/90))*sin(2*pi/45):=
begin
have : (-2) * (sin((-29) * pi / 90) * cos(-pi / 6) - sin(-pi / 6) * cos((-29) * pi / 90)) * sin(2 * pi / 45) = -2*(sin(-29*pi/90)*cos(-pi/6) - sin(-pi/6)*cos(-29*pi/90))*sin(2*pi/45),
{
field_simp at *,
},
have : sin(-7*pi/45) = sin(-29*pi/90) * cos(-pi/6) - sin(-pi/6) * cos(-29*pi/90),
{
have : sin(-7*pi/45) = sin((-29*pi/90) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/9) - cos(pi/5) = - 2 * sin(-7*pi/45) * sin(2*pi/45),
{
rw cos_sub_cos,
have : sin(((-pi/9) + (pi/5))/2) = sin(2*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/9) - (pi/5))/2) = sin(-7*pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_978 : sin(3081*pi/2)=- sin(1511*pi/2):=
begin
have : sin(pi/2) = sin(3081*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (770),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - sin(1511*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (377),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_979 : cos(pi/9)=cos(-2483*pi/9):=
begin
have : cos((-2483) * pi / 9) = cos(-2483*pi/9),
{
field_simp at *,
},
have : sin(34387*pi/18) = cos(-2483*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (34387*pi/18) (817),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/9) = sin(34387*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (955),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_980 : -sin(286*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(pi/3) = -sin(286*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (47),
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


lemma Trigo_number_generalization_step1_981 : cos(pi/8) ** 2=1 - (sin(-pi/24)*cos(-pi/6) - sin(-pi/6)*cos(-pi/24))**2:=
begin
have : sin(pi/8) = sin(-pi/24) * cos(-pi/6) - sin(-pi/6) * cos(-pi/24),
{
have : sin(pi/8) = sin((-pi/24) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) ** 2 = 1 - sin(pi/8) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_982 : sin(pi/2)*cos(1847*pi/18)=cos(-11*pi/18) / 2 - cos(7*pi/18) / 2:=
begin
have : cos(1847 * pi / 18) * sin(pi / 2) = sin(pi/2)*cos(1847*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) = cos(1847*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/9) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/9) * sin(pi/2) = cos(-11*pi/18) / 2 - cos(7*pi/18) / 2,
{
rw sin_mul_sin,
have : cos((-pi/9) + (pi/2)) = cos(7*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/9) - (pi/2)) = cos(-11*pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_983 (h0 : tan(2967*pi/4)≠ 0) : -1/tan(2967*pi/4)=- tan(551*pi/4):=
begin
have : (-1) / tan(2967 * pi / 4) = -1/tan(2967*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(2967*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (741),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = - tan(551*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (138),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_984 : -3*cos(pi/3) + 4*cos(pi/3)**3=cos(1333*pi):=
begin
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
have : cos(pi) = cos(1333*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (667),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_985 : -2*sin(pi/14)**2 + cos(pi/4) + 1=2 * cos(-3*pi/56) * cos(11*pi/56):=
begin
have : 1 - 2 * sin(pi / 14) ** 2 + cos(pi / 4) = -2*sin(pi/14)**2 + cos(pi/4) + 1,
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
have : cos(pi/7) + cos(pi/4) = 2 * cos(-3*pi/56) * cos(11*pi/56),
{
rw cos_add_cos,
have : cos(((pi/7) + (pi/4))/2) = cos(11*pi/56),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/7) - (pi/4))/2) = cos(-3*pi/56),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_986 : sin(157*pi/4) + cos(pi/2)=- 2 * sin(pi/8) * sin(3*pi/8):=
begin
have : cos(pi / 2) - -sin(157 * pi / 4) = sin(157*pi/4) + cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(157*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) - cos(pi/4) = - 2 * sin(pi/8) * sin(3*pi/8),
{
rw cos_sub_cos,
have : sin(((pi/2) + (pi/4))/2) = sin(3*pi/8),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (pi/4))/2) = sin(pi/8),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_987 (h0 : cos(pi)≠ 0) : sin(pi)/cos(pi)=0:=
begin
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


lemma Trigo_number_generalization_step1_988 : -tan(1103*pi/4)=1:=
begin
have : tan(pi/4) = -tan(1103*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (276),
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


lemma Trigo_number_generalization_step1_989 : cos(2*pi)=-sin(381*pi)**2 + cos(pi)**2:=
begin
have : -(-sin(381 * pi)) ** 2 + cos(pi) ** 2 = -sin(381*pi)**2 + cos(pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -sin(381*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (191),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_number_generalization_step1_990 : (sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))*sin(-pi/2)=cos(-3*pi/2) / 2 - cos(pi/2) / 2:=
begin
have : sin(-pi / 2) * (sin(-pi) * cos(2 * pi) + sin(2 * pi) * cos(-pi)) = (sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))*sin(-pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(-pi) * cos(2*pi) + sin(2*pi) * cos(-pi),
{
have : sin(pi) = sin((-pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * sin(pi) = cos(-3*pi/2) / 2 - cos(pi/2) / 2,
{
rw sin_mul_sin,
have : cos((-pi/2) + (pi)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (pi)) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_991 : cos(5363*pi/4)=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/4) = cos(5363*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/4) (670),
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


lemma Trigo_number_generalization_step1_992 : cos(pi/7) ** 2=1 - cos(4727*pi/14)**2:=
begin
have : sin(pi/7) = cos(4727*pi/14),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/7) (168),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/7) ** 2 = 1 - sin(pi/7) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_number_generalization_step1_993 : tan(5951*pi/6)=- tan(3067*pi/6):=
begin
have : tan(-pi/6) = tan(5951*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (992),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - tan(3067*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/6) (511),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_994 (h0 : (1-2*sin(-pi)**2)≠ 0) : tan(-2*pi)=sin(-2*pi)/(1 - 2*sin(-pi)**2):=
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


lemma Trigo_number_generalization_step1_995 : -3*cos(pi/3) + 4*cos(pi/3)**3=- 1:=
begin
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
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_number_generalization_step1_996 : -sin(pi)*cos(5*pi/4) + sin(5*pi/4)*cos(pi)=sqrt( 2 ) / 2:=
begin
have : sin(5 * pi / 4) * cos(pi) - sin(pi) * cos(5 * pi / 4) = -sin(pi)*cos(5*pi/4) + sin(5*pi/4)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(5*pi/4) * cos(pi) - sin(pi) * cos(5*pi/4),
{
have : sin(pi/4) = sin((5*pi/4) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sqrt( 2 ) / 2,
{
rw sin_pi_div_four,
},
rw this,
end


lemma Trigo_number_generalization_step1_997 : tan(5464*pi/9)=- 1 / tan(11459*pi/18):=
begin
have : tan(pi/9) = tan(5464*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (607),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = - 1 / tan(11459*pi/18),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/9) (636),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_998 : -sin(1049*pi/7)=- cos(2669*pi/14):=
begin
have : sin(pi/7) = -sin(1049*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/7) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/7) = - cos(2669*pi/14),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/7) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_999 : -sin(6389*pi/4)*cos(pi/2)=cos(pi/4) / 2 + cos(3*pi/4) / 2:=
begin
have : cos(pi / 2) * -sin(6389 * pi / 4) = -sin(6389*pi/4)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(6389*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (798),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) * cos(pi/4) = cos(pi/4) / 2 + cos(3*pi/4) / 2,
{
rw cos_mul_cos,
have : cos((pi/2) + (pi/4)) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/2) - (pi/4)) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_number_generalization_step1_1000 : 1 - 2*sin(-pi/2)**2=cos(1999*pi):=
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
have : cos(-pi) = cos(1999*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (999),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_number_generalization_step1_1001 : -sin(5873*pi/3)=cos(3215*pi/6):=
begin
have : cos(-pi/6) = -sin(5873*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (978),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(3215*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (268),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end
