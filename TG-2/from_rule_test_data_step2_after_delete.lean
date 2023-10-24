import trigo_import
open real
open_locale real
variables (x y : ℝ)


lemma Trigo_0_test : cos(334*pi/3)**2=1 - cos(533*pi/6)**2:=
begin
have : (-cos(334 * pi / 3)) ** 2 = cos(334*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(334*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (-cos(533 * pi / 6)) ** 2 = 1 - cos(533*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -cos(533*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (44),
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




lemma Trigo_2_test (h0 : sin(7*pi/12)≠ 0) (h1 : sin(7*pi/12)≠ 0) (h2 : (2*sin(7*pi/12))≠ 0) : -sin(68*pi) + sin(pi/6)=sin(-5*pi/12)*sin(7*pi/6)/sin(7*pi/12):=
begin
have : 2 * sin((-5) * pi / 12) * (sin(7 * pi / 6) / (2 * sin(7 * pi / 12))) = sin(-5*pi/12)*sin(7*pi/6)/sin(7*pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi / 6) - sin(68 * pi) = -sin(68*pi) + sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(68*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (34),
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


lemma Trigo_3_test : sin(pi/3) - sin(2*pi)=2*sin(-5*pi/6)*cos(233*pi/6):=
begin
have : 2 * sin((-5) * pi / 6) * cos(233 * pi / 6) = 2*sin(-5*pi/6)*cos(233*pi/6),
{
field_simp at *,
},
have : cos(355*pi/6) = cos(233*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (355*pi/6) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin((-5) * pi / 6) * cos(355 * pi / 6) = 2*sin(-5*pi/6)*cos(355*pi/6),
{
field_simp at *,
},
have : cos(7*pi/6) = cos(355*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (7*pi/6) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) - sin(2*pi) = 2 * sin(-5*pi/6) * cos(7*pi/6),
{
rw sin_sub_sin,
have : cos(((pi/3) + (2*pi))/2) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (2*pi))/2) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_4_test : 1 - 2*sin(-7*pi/12)**2=(1 - 2*sin(-pi/2)**2)*cos(-pi/6) - sin(-pi)*sin(-pi/6):=
begin
have : -sin(-pi) * sin(-pi / 6) + (1 - 2 * sin(-pi / 2) ** 2) * cos(-pi / 6) = (1 - 2*sin(-pi/2)**2)*cos(-pi/6) - sin(-pi)*sin(-pi/6),
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
have : 1 - 2 * sin((-7) * pi / 12) ** 2 = 1 - 2*sin(-7*pi/12)**2,
{
field_simp at *,
},
have : cos(-7*pi/6) = 1 - 2 * sin(-7*pi/12) ** 2,
{
have : cos(-7*pi/6) = cos(2*(-7*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
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


lemma Trigo_5_test : 2*(-sin(-pi/12)*sin(pi/3) + cos(-pi/12)*cos(pi/3))*sin(pi/4)=1:=
begin
have : 2 * sin(pi / 4) * (-sin(-pi / 12) * sin(pi / 3) + cos(-pi / 12) * cos(pi / 3)) = 2*(-sin(-pi/12)*sin(pi/3) + cos(-pi/12)*cos(pi/3))*sin(pi/4),
{
field_simp at *,
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


lemma Trigo_6_test : -sin(1073*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(709*pi/12) = sin(1073*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (709*pi/12) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(709*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (29),
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


lemma Trigo_7_test : sin(240*pi)**2=1 - cos(2*pi) ** 2:=
begin
have : (-sin(240 * pi)) ** 2 = sin(240*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(169*pi/2) = -sin(240*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (169*pi/2) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(169 * pi / 2)) ** 2 = cos(169*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(169*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (41),
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


lemma Trigo_8_test : sin(pi/3) + sin(-pi/6)=(-2*sin(pi/8)**2 + 2*cos(1417*pi/8)**2)*sin(pi/12):=
begin
have : 2 * (-sin(pi / 8) ** 2 + (-cos(1417 * pi / 8)) ** 2) * sin(pi / 12) = (-2*sin(pi/8)**2 + 2*cos(1417*pi/8)**2)*sin(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/8) = -cos(1417*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/8) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin(pi / 12) * (-sin(pi / 8) ** 2 + cos(pi / 8) ** 2) = 2*(-sin(pi/8)**2 + cos(pi/8)**2)*sin(pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
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


lemma Trigo_9_test : 2*sin(63*pi/2)*cos(63*pi/2)=0:=
begin
have : sin(63*pi) = 2 * sin(63*pi/2) * cos(63*pi/2),
{
have : sin(63*pi) = sin(2*(63*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(63*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (31),
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


lemma Trigo_10_test : -(sin(-2*pi)*cos(5*pi/2) + sin(5*pi/2)*cos(-2*pi))**2 + cos(pi/2)**2=cos(79*pi):=
begin
have : -(sin(5 * pi / 2) * cos((-2) * pi) + sin((-2) * pi) * cos(5 * pi / 2)) ** 2 + cos(pi / 2) ** 2 = -(sin(-2*pi)*cos(5*pi/2) + sin(5*pi/2)*cos(-2*pi))**2 + cos(pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(5*pi/2) * cos(-2*pi) + sin(-2*pi) * cos(5*pi/2),
{
have : sin(pi/2) = sin((5*pi/2) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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
have : cos(pi) = cos(79*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_11_test : -cos(665*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(275*pi/12) = -cos(665*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (275*pi/12) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(275*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (11),
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


lemma Trigo_12_test (h0 : cos(-pi/2)≠ 0) (h1 : (2*cos(-pi/2))≠ 0) (h2 : (2*cos(41*pi/2))≠ 0) : sin(-pi)/(2*cos(41*pi/2))=cos(65*pi):=
begin
have : cos(-pi/2) = cos(41*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
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
have : sin(-pi/2) = cos(65*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_13_test (h0 : sin(821*pi/6)≠ 0) (h1 : (2*sin(821*pi/6))≠ 0) : -sin(821*pi/3)/(2*sin(821*pi/6))=sqrt( 3 ) / 2:=
begin
have : -(sin(821 * pi / 3) / (2 * sin(821 * pi / 6))) = -sin(821*pi/3)/(2*sin(821*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(821*pi/6) = sin(821*pi/3) / ( 2 * sin(821*pi/6) ),
{
have : sin(821*pi/3) = sin(2*(821*pi/6)),
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
have : cos(pi/6) = -cos(821*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (68),
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


lemma Trigo_14_test : 4*cos(253*pi/4)**3 - 3*cos(253*pi/4)=sqrt( 2 ) / 2:=
begin
have : (-4) * (-cos(253 * pi / 4)) ** 3 + 3 * -cos(253 * pi / 4) = 4*cos(253*pi/4)**3 - 3*cos(253*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(253*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (31),
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


lemma Trigo_15_test : sin(517*pi/3)=-cos(427*pi/6):=
begin
have : cos(pi/6) = sin(517*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(122*pi/3) = -cos(427*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (122*pi/3) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(122*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_16_test : -1 + 2*cos(515*pi/12)**2=- cos(893*pi/6):=
begin
have : 2 * cos(515 * pi / 12) ** 2 - 1 = -1 + 2*cos(515*pi/12)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(515*pi/6) = 2 * cos(515*pi/12) ** 2 - 1,
{
have : cos(515*pi/6) = cos(2*(515*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(515*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(893*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_17_test : sin(679*pi/6)*cos(-pi/3) + sin(-pi/3)*cos(679*pi/6)=1 / 2:=
begin
have : sin(677*pi/6) = sin(679*pi/6) * cos(-pi/3) + sin(-pi/3) * cos(679*pi/6),
{
have : sin(677*pi/6) = sin((679*pi/6) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(677*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi/6) (56),
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


lemma Trigo_18_test : (sin(-2*pi)*cos(7*pi/3) + (sin(11*pi/6)*cos(pi/2) + sin(pi/2)*cos(11*pi/6))*cos(-2*pi))*cos(-pi)=- sin(-4*pi/3) / 2 + sin(-2*pi/3) / 2:=
begin
have : (sin((-2) * pi) * cos(7 * pi / 3) + (sin(11 * pi / 6) * cos(pi / 2) + sin(pi / 2) * cos(11 * pi / 6)) * cos((-2) * pi)) * cos(-pi) = (sin(-2*pi)*cos(7*pi/3) + (sin(11*pi/6)*cos(pi/2) + sin(pi/2)*cos(11*pi/6))*cos(-2*pi))*cos(-pi),
{
field_simp at *,
},
have : sin(7*pi/3) = sin(11*pi/6) * cos(pi/2) + sin(pi/2) * cos(11*pi/6),
{
have : sin(7*pi/3) = sin((11*pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(7 * pi / 3) * cos((-2) * pi) + sin((-2) * pi) * cos(7 * pi / 3)) * cos(-pi) = (sin(-2*pi)*cos(7*pi/3) + sin(7*pi/3)*cos(-2*pi))*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(7*pi/3) * cos(-2*pi) + sin(-2*pi) * cos(7*pi/3),
{
have : sin(pi/3) = sin((7*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(-pi) = - sin(-4*pi/3) / 2 + sin(-2*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi) + (pi/3)) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (pi/3)) = sin(-4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_19_test : -(3*sin(919*pi/18) - 4*sin(919*pi/18)**3)*cos(pi/3)=- sin(pi/6) / 2 + sin(pi/2) / 2:=
begin
have : -((-4) * sin(919 * pi / 18) ** 3 + 3 * sin(919 * pi / 18)) * cos(pi / 3) = -(3*sin(919*pi/18) - 4*sin(919*pi/18)**3)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(919*pi/6) = -4 * sin(919*pi/18) ** 3 + 3 * sin(919*pi/18),
{
have : sin(919*pi/6) = sin(3*(919*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(919*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(pi/3) = - sin(pi/6) / 2 + sin(pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
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
ring,
},
rw this,
end


lemma Trigo_20_test : 1 - 2*cos(473*pi/4)**2=- sin(32*pi):=
begin
have : sin(pi/4) = cos(473*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (59),
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
have : cos(pi/2) = - sin(32*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_21_test : sin(-2*pi)*sin(430*pi/3) - cos(-2*pi)*cos(430*pi/3)=- sin(703*pi/6):=
begin
have : -(-sin(430 * pi / 3) * sin((-2) * pi) + cos(430 * pi / 3) * cos((-2) * pi)) = sin(-2*pi)*sin(430*pi/3) - cos(-2*pi)*cos(430*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(424*pi/3) = -sin(430*pi/3) * sin(-2*pi) + cos(430*pi/3) * cos(-2*pi),
{
have : cos(424*pi/3) = cos((430*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(424*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - sin(703*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_23_test : -4*cos(677*pi/18)**3 + 3*cos(677*pi/18)=sqrt( 3 ) / 2:=
begin
have : (-4) * cos(677 * pi / 18) ** 3 + 3 * cos(677 * pi / 18) = -4*cos(677*pi/18)**3 + 3*cos(677*pi/18),
{
field_simp at *,
},
have : sin(pi/9) = cos(677*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (18),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_24_test : sin(-pi/3) + sin(2*pi)=-2*(cos(pi/3)*cos(409*pi/6) + sin(pi/3)*sin(409*pi/6))*sin(5*pi/6):=
begin
have : (-2) * sin(5 * pi / 6) * (sin(409 * pi / 6) * sin(pi / 3) + cos(409 * pi / 6) * cos(pi / 3)) = -2*(cos(pi/3)*cos(409*pi/6) + sin(pi/3)*sin(409*pi/6))*sin(5*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(407*pi/6) = sin(409*pi/6) * sin(pi/3) + cos(409*pi/6) * cos(pi/3),
{
have : cos(407*pi/6) = cos((409*pi/6) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin(5 * pi / 6) * -cos(407 * pi / 6) = -2*sin(5*pi/6)*cos(407*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-7*pi/6) = -cos(407*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-7*pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_25_test : cos(pi/2)*cos(361*pi/3) + sin(pi/2)*sin(361*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(361 * pi / 3) * sin(pi / 2) + cos(361 * pi / 3) * cos(pi / 2) = cos(pi/2)*cos(361*pi/3) + sin(pi/2)*sin(361*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(719*pi/6) = sin(361*pi/3) * sin(pi/2) + cos(361*pi/3) * cos(pi/2),
{
have : cos(719*pi/6) = cos((361*pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(719*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (60),
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


lemma Trigo_26_test : -cos(115*pi)=cos(192*pi):=
begin
have : cos(55*pi) = cos(115*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (55*pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -cos(55*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(192*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_27_test : (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(pi/6) - sin(-pi/6)*cos(pi/6)=- sin(70*pi/3):=
begin
have : sin(pi / 6) * (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) - sin(-pi / 6) * cos(pi / 6) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(pi/6) - sin(-pi/6)*cos(pi/6),
{
field_simp at *,
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
have : sin(pi/3) = - sin(70*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_28_test (h0 : cos((-2*pi)/2)≠ 0) (h1 : (1+cos(-2*pi))≠ 0) (h2 : (1+cos((-2)*pi))≠ 0) : cos(387*pi/2)/(1 + cos(-2*pi))=1 / tan(199*pi/2):=
begin
have : cos(387 * pi / 2) / (1 + cos((-2) * pi)) = cos(387*pi/2)/(1 + cos(-2*pi)),
{
field_simp at *,
},
have : sin(-2*pi) = cos(387*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(-pi) = 1 / tan(199*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_29_test : sin(-7*pi/6)=(-1 + 2*cos(-pi/12)**2)*sin(-pi) - sin(-pi/6)*cos(166*pi):=
begin
have : (-1 + 2 * cos(-pi / 12) ** 2) * sin(-pi) + sin(-pi / 6) * -cos(166 * pi) = (-1 + 2*cos(-pi/12)**2)*sin(-pi) - sin(-pi/6)*cos(166*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -cos(166*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 6) * cos(-pi) + sin(-pi) * (2 * cos(-pi / 12) ** 2 - 1) = (-1 + 2*cos(-pi/12)**2)*sin(-pi) + sin(-pi/6)*cos(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-7*pi/6) = sin(-pi/6) * cos(-pi) + sin(-pi) * cos(-pi/6),
{
have : sin(-7*pi/6) = sin((-pi/6) + (-pi)),
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


lemma Trigo_30_test : sin(13*pi/6)=sin(2*pi)*cos(983*pi/6) - sin(pi/6)*sin(75*pi/2):=
begin
have : cos(pi/6) = cos(983*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2 * pi) * cos(pi / 6) + sin(pi / 6) * -sin(75 * pi / 2) = sin(2*pi)*cos(pi/6) - sin(pi/6)*sin(75*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -sin(75*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(13*pi/6) = sin(2*pi) * cos(pi/6) + sin(pi/6) * cos(2*pi),
{
have : sin(13*pi/6) = sin((2*pi) + (pi/6)),
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


lemma Trigo_31_test : -4*sin(29*pi/6)**3 + 3*sin(29*pi/6)=sin(53*pi/2):=
begin
have : (-4) * sin(29 * pi / 6) ** 3 + 3 * sin(29 * pi / 6) = -4*sin(29*pi/6)**3 + 3*sin(29*pi/6),
{
field_simp at *,
},
have : sin(29*pi/2) = -4 * sin(29*pi/6) ** 3 + 3 * sin(29*pi/6),
{
have : sin(29*pi/2) = sin(3*(29*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(29*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(53*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_32_test : sin(-2*pi) * sin(2*pi)=-cos(0)/2 + cos(pi/2)*cos(287*pi/2)/2 + sin(-7*pi/2)*sin(pi/2)/2:=
begin
have : -cos(0) / 2 + cos(287 * pi / 2) * cos(pi / 2) / 2 + sin((-7) * pi / 2) * sin(pi / 2) / 2 = -cos(0)/2 + cos(pi/2)*cos(287*pi/2)/2 + sin(-7*pi/2)*sin(pi/2)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-7*pi/2) = cos(287*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (sin((-7) * pi / 2) * sin(pi / 2) + cos((-7) * pi / 2) * cos(pi / 2)) / 2 - cos(0) / 2 = -cos(0)/2 + cos(-7*pi/2)*cos(pi/2)/2 + sin(-7*pi/2)*sin(pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi) = sin(-7*pi/2) * sin(pi/2) + cos(-7*pi/2) * cos(pi/2),
{
have : cos(-4*pi) = cos((-7*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * sin(2*pi) = cos(-4*pi) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
have : cos((-2*pi) + (2*pi)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (2*pi)) = cos(-4*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_33_test : 1 - 2*sin(-pi/4)**2=cos(309*pi/2):=
begin
have : - -cos(309 * pi / 2) = cos(309*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(63*pi/2) = -cos(309*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (63*pi/2) (61),
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


lemma Trigo_34_test : cos(-pi/6)*cos(737*pi/6) - sin(-pi/6)*sin(7*pi/6)=- 1:=
begin
have : cos(7*pi/6) = cos(737*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (7*pi/6) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(7 * pi / 6) * sin(-pi / 6) + cos(7 * pi / 6) * cos(-pi / 6) = cos(-pi/6)*cos(7*pi/6) - sin(-pi/6)*sin(7*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(7*pi/6) * sin(-pi/6) + cos(7*pi/6) * cos(-pi/6),
{
have : cos(pi) = cos((7*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_35_test : -cos(1657*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(727*pi/6) = -cos(1657*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (727*pi/6) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = cos(727*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/6) (61),
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


lemma Trigo_36_test : sin(343*pi/3)*cos(pi/2)=cos(-pi/2)*cos(-pi/6):=
begin
have : 1 / 2 * (2 * cos(-pi / 2) * cos(-pi / 6)) = cos(-pi/2)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) + cos(pi/3) = 2 * cos(-pi/2) * cos(-pi/6),
{
rw cos_add_cos,
have : cos(((-2*pi/3) + (pi/3))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi/3) - (pi/3))/2) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(-2*pi/3) + cos(pi/3)) = cos(-2*pi/3)/2+cos(pi/3)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-pi/6) = sin(343*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) * cos(pi/2) = cos(-2*pi/3) / 2 + cos(pi/3) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (pi/2)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (pi/2)) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_37_test : sin(-2*pi)**2 + (cos(-5*pi/3)*cos(319*pi/3) - sin(-5*pi/3)*sin(-pi/3))**2=1:=
begin
have : sin((-2) * pi) ** 2 + (cos((-5) * pi / 3) * cos(319 * pi / 3) - sin((-5) * pi / 3) * sin(-pi / 3)) ** 2 = sin(-2*pi)**2 + (cos(-5*pi/3)*cos(319*pi/3) - sin(-5*pi/3)*sin(-pi/3))**2,
{
field_simp at *,
},
have : cos(-pi/3) = cos(319*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi) ** 2 + (-sin((-5) * pi / 3) * sin(-pi / 3) + cos((-5) * pi / 3) * cos(-pi / 3)) ** 2 = sin(-2*pi)**2 + (cos(-5*pi/3)*cos(-pi/3) - sin(-5*pi/3)*sin(-pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(-2*pi) ** 2 + cos(-2*pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_38_test : -sin(74*pi/3)=-(-sin(pi)*cos(4*pi/3) + sin(4*pi/3)*cos(pi))*sin(pi/2) + cos(pi/3)*cos(pi/2):=
begin
have : cos(5*pi/6) = -sin(74*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(4 * pi / 3) * cos(pi) - sin(pi) * cos(4 * pi / 3)) * sin(pi / 2) + cos(pi / 3) * cos(pi / 2) = -(-sin(pi)*cos(4*pi/3) + sin(4*pi/3)*cos(pi))*sin(pi/2) + cos(pi/3)*cos(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = sin(4*pi/3) * cos(pi) - sin(pi) * cos(4*pi/3),
{
have : sin(pi/3) = sin((4*pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
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


lemma Trigo_39_test (h0 : cos(pi/2)≠ 0) : tan(pi/2)=2*(-sin(0)/2 + sin(pi/2)/2)/cos(pi/2):=
begin
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
have : 2*(sin(pi/4) * cos(pi/4))/cos(pi/2) = 2*sin(pi/4)*cos(pi/4)/cos(pi/2),
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
conv {to_rhs, rw ← this,},
have : tan(pi/2) = sin(pi/2) / cos(pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_40_test : cos(2953*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(1105*pi/12) = cos(2953*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (1105*pi/12) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = cos(1105*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/12) (46),
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


lemma Trigo_41_test (h0 : (4*cos(-pi/3)**3-3*cos(-pi/3))≠ 0) (h1 : (-3*cos(-pi/3)+4*cos(-pi/3)**3)≠ 0) (h2 : ((-3)*-sin(239*pi/6)+4*(-sin(239*pi/6))**3)≠ 0) (h3 : (3*sin(239*pi/6)-4*sin(239*pi/6)**3)≠ 0) : tan(-pi)=sin(-pi)/(3*sin(239*pi/6) - 4*sin(239*pi/6)**3):=
begin
have : sin(-pi) / ((-3) * -sin(239 * pi / 6) + 4 * (-sin(239 * pi / 6)) ** 3) = sin(-pi)/(3*sin(239*pi/6) - 4*sin(239*pi/6)**3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -sin(239*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) / (4 * cos(-pi / 3) ** 3 - 3 * cos(-pi / 3)) = sin(-pi)/(-3*cos(-pi/3) + 4*cos(-pi/3)**3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(-pi) = sin(-pi) / cos(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_42_test (h0 : cos(3*pi/4)≠ 0) (h1 : sin(161*pi/4)≠ 0) (h2 : -sin(161*pi/4)≠ 0) : -sin(3*pi/4)/sin(161*pi/4)=- 1:=
begin
have : sin(3 * pi / 4) / -sin(161 * pi / 4) = -sin(3*pi/4)/sin(161*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(161*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (19),
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


lemma Trigo_43_test : cos(-pi/6)=-sin(2*pi)*cos(655*pi/3) + sin(655*pi/3)*cos(2*pi):=
begin
have : sin(655 * pi / 3) * cos(2 * pi) - sin(2 * pi) * cos(655 * pi / 3) = -sin(2*pi)*cos(655*pi/3) + sin(655*pi/3)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(649*pi/3) = sin(655*pi/3) * cos(2*pi) - sin(2*pi) * cos(655*pi/3),
{
have : sin(649*pi/3) = sin((655*pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(391*pi/3) = sin(649*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (391*pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(391*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_44_test : cos(161*pi)=cos(pi):=
begin
have : - -cos(161 * pi) = cos(161*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi) = -cos(161*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (8*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -cos(8*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (0),
focus{repeat {apply congr_arg _}},
simp,
},
rw this,
end


lemma Trigo_45_test : 6*sin(-pi/6)*cos(-pi/6) - 32*sin(-pi/6)**3*cos(-pi/6)**3=sin(115*pi):=
begin
have : 3 * (2 * sin(-pi / 6) * cos(-pi / 6)) - 4 * (2 * sin(-pi / 6) * cos(-pi / 6)) ** 3 = 6*sin(-pi/6)*cos(-pi/6) - 32*sin(-pi/6)**3*cos(-pi/6)**3,
{
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
have : sin(-pi) = sin(115*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_46_test : -cos(455*pi/3)*cos(523*pi/3)=- sin(pi/2) / 2 + sin(pi/6) / 2:=
begin
have : sin(-pi/6) = -cos(455*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(523*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(pi/3) = - sin(pi/2) / 2 + sin(pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/6)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/6)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_47_test : (-(sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))**2 + cos(pi)**2)*cos(-pi/6)=cos(13*pi/6) / 2 + cos(11*pi/6) / 2:=
begin
have : (-(sin(2 * pi) * cos(-pi) + sin(-pi) * cos(2 * pi)) ** 2 + cos(pi) ** 2) * cos(-pi / 6) = (-(sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))**2 + cos(pi)**2)*cos(-pi/6),
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


lemma Trigo_48_test : 2*(1 - 2*sin(pi/8)**2)*sin(pi/4)=- cos(169*pi):=
begin
have : 2 * sin(pi / 4) * (1 - 2 * sin(pi / 8) ** 2) = 2*(1 - 2*sin(pi/8)**2)*sin(pi/4),
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
have : sin(pi/2) = - cos(169*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_49_test : cos(317*pi/3)=cos(647*pi/3):=
begin
have : cos(pi/3) = cos(317*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(373*pi/6) = cos(647*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (373*pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(373*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_50_test : -2*sin(-pi/2)*sin(291*pi/2)*cos(-pi/2)=sin(pi) / 2 + sin(-3*pi) / 2:=
begin
have : -(2 * sin(-pi / 2) * cos(-pi / 2)) * sin(291 * pi / 2) = -2*sin(-pi/2)*sin(291*pi/2)*cos(-pi/2),
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
have : sin(-pi) * -sin(291 * pi / 2) = -sin(-pi)*sin(291*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(291*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (71),
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


lemma Trigo_51_test : -1 + 2*(cos(pi/6)*cos(pi/2) + sin(pi/6)*sin(pi/2))**2=- 1 / 2:=
begin
have : -1 + 2 * (sin(pi / 2) * sin(pi / 6) + cos(pi / 2) * cos(pi / 6)) ** 2 = -1 + 2*(cos(pi/6)*cos(pi/2) + sin(pi/6)*sin(pi/2))**2,
{
field_simp at *,
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


lemma Trigo_52_test : sin(-pi)*sin(341*pi/3) - cos(-pi)*cos(341*pi/3)=1 / 2:=
begin
have : -(-sin(341 * pi / 3) * sin(-pi) + cos(341 * pi / 3) * cos(-pi)) = sin(-pi)*sin(341*pi/3) - cos(-pi)*cos(341*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(338*pi/3) = -sin(341*pi/3) * sin(-pi) + cos(341*pi/3) * cos(-pi),
{
have : cos(338*pi/3) = cos((341*pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(338*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (56),
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


lemma Trigo_53_test : sin(190*pi)**2=sin(339*pi/2)/2 + 1/2:=
begin
have : 1 / 2 - -sin(339 * pi / 2) / 2 = sin(339*pi/2)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-4*pi) = -sin(339*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-4*pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = sin(190*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
rw this,
end


lemma Trigo_54_test (h0 : cos(pi)≠ 0) : -4*sin(79*pi/3)**3 + 3*sin(79*pi/3)=sin(2*pi) / ( 2 * cos(pi) ):=
begin
have : (-4) * sin(79 * pi / 3) ** 3 + 3 * sin(79 * pi / 3) = -4*sin(79*pi/3)**3 + 3*sin(79*pi/3),
{
field_simp at *,
},
have : sin(pi/3) = sin(79*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (13),
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


lemma Trigo_55_test : -sin(238*pi)=cos(181*pi/2):=
begin
have : sin(156*pi) = sin(238*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (156*pi) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(156*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(181*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_56_test (h0 : sin(-3*pi/2)≠ 0) (h1 : (2*sin((-3)*pi/2))≠ 0) (h2 : sin(-3*pi/2)≠ 0) : sin(pi) - sin(72*pi)=sin(-3*pi)*sin(-pi/2)/sin(-3*pi/2):=
begin
have : -sin(72 * pi) + sin(pi) = sin(pi) - sin(72*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(72*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 2) * (sin((-3) * pi) / (2 * sin((-3) * pi / 2))) = sin(-3*pi)*sin(-pi/2)/sin(-3*pi/2),
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
have : sin(-2*pi) + sin(pi) = 2 * sin(-pi/2) * cos(-3*pi/2),
{
rw sin_add_sin,
have : sin(((-2*pi) + (pi))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-2*pi) - (pi))/2) = cos(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_57_test : cos(261*pi)=- sin(197*pi/2):=
begin
have : - -cos(261 * pi) = cos(261*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(110*pi) = -cos(261*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (110*pi) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -cos(110*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(197*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_58_test : cos(1031*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos(1031 * pi / 6) = cos(1031*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(689*pi/6) = -cos(1031*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (689*pi/6) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(689*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (57),
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


lemma Trigo_59_test : -(sin(263*pi/3)*cos(pi/6) - sin(pi/6)*cos(263*pi/3))*cos(-pi/2)=- sin(-pi) / 2 + sin(0) / 2:=
begin
have : sin(175*pi/2) = sin(263*pi/3) * cos(pi/6) - sin(pi/6) * cos(263*pi/3),
{
have : sin(175*pi/2) = sin((263*pi/3) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(175*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(-pi/2) = - sin(-pi) / 2 + sin(0) / 2,
{
rw mul_comm,
rw cos_mul_sin,
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
ring,
},
rw this,
end


lemma Trigo_60_test : -sin(3*pi)=- sin(180*pi):=
begin
have : sin(73*pi) = -sin(3*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (73*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(73*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(180*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_61_test : cos(-pi/3)*cos(pi) - sin(-pi/3)*cos(271*pi/2)=- 1 / 2:=
begin
have : sin(pi) = cos(271*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_62_test : sin(1445*pi/6)=1 / 2:=
begin
have : - -sin(1445 * pi / 6) = sin(1445*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(520*pi/3) = -sin(1445*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (520*pi/3) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = -cos(520*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (86),
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


lemma Trigo_63_test : -sin(-363*pi/2)=cos(117*pi):=
begin
have : -sin((-363) * pi / 2) = -sin(-363*pi/2),
{
field_simp at *,
},
have : cos(188*pi) = sin(-363*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (188*pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(188*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(117*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_64_test : sin(72*pi)=sin(pi)*cos(2*pi) + sin(2*pi)*cos(121*pi):=
begin
have : sin(3*pi) = sin(72*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) * cos(121 * pi) + sin(pi) * cos(2 * pi) = sin(pi)*cos(2*pi) + sin(2*pi)*cos(121*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = cos(121*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi) = sin(2*pi) * cos(pi) + sin(pi) * cos(2*pi),
{
have : sin(3*pi) = sin((2*pi) + (pi)),
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


lemma Trigo_65_test : sin(297*pi/2)=1:=
begin
have : - -sin(297 * pi / 2) = sin(297*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(91*pi) = -sin(297*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (91*pi) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(91*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (45),
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


lemma Trigo_66_test : -sin(pi/2)**2 + cos(149*pi/2)**2=- 1:=
begin
have : cos(pi/2) = cos(149*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (37),
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
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_67_test : -sin(784*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(1109*pi/6) = sin(784*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (1109*pi/6) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(1109*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (92),
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


lemma Trigo_68_test : cos(-5*pi/6)/2 + cos(pi/2)/2 - sin(-pi/6)*sin(2*pi/3)=0:=
begin
have : cos((-5) * pi / 6) / 2 + cos(pi / 2) / 2 - sin(-pi / 6) * sin(2 * pi / 3) = cos(-5*pi/6)/2 + cos(pi/2)/2 - sin(-pi/6)*sin(2*pi/3),
{
field_simp at *,
},
have : cos(-pi/6) * cos(2*pi/3) = cos(-5*pi/6) / 2 + cos(pi/2) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (2*pi/3)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (2*pi/3)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(-pi/6) * cos(2*pi/3)) = cos(-pi/6)*cos(2*pi/3),
{
ring,
},
have : -sin(2 * pi / 3) * sin(-pi / 6) + cos(2 * pi / 3) * cos(-pi / 6) = cos(-pi/6)*cos(2*pi/3) - sin(-pi/6)*sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(2*pi/3) * sin(-pi/6) + cos(2*pi/3) * cos(-pi/6),
{
have : cos(pi/2) = cos((2*pi/3) + (-pi/6)),
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




lemma Trigo_70_test : cos(-3*pi/2)=cos(165*pi)*cos(375*pi/2) + cos(pi/2)*cos(2*pi):=
begin
have : - -cos(375 * pi / 2) * cos(165 * pi) + cos(pi / 2) * cos(2 * pi) = cos(165*pi)*cos(375*pi/2) + cos(pi/2)*cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -cos(375*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -cos(165 * pi) * sin(2 * pi) + cos(pi / 2) * cos(2 * pi) = -sin(2*pi)*cos(165*pi) + cos(pi/2)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = -cos(165*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (82),
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


lemma Trigo_71_test : cos(-1465*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -cos((-1465) * pi / 12) = cos(-1465*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2293*pi/12) = -cos(-1465*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2293*pi/12) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(2293*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (95),
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


lemma Trigo_72_test : sin(-pi/2)=1 - 2*sin(35*pi/2)**2:=
begin
have : 1 - 2 * (-sin(35 * pi / 2)) ** 2 = 1 - 2*sin(35*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(70*pi) = -sin(35*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (70*pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(2 * cos(70 * pi) ** 2 - 1) = 1 - 2*cos(70*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(140*pi) = 2 * cos(70*pi) ** 2 - 1,
{
have : cos(140*pi) = cos(2*(70*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
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


lemma Trigo_73_test (h0 : tan(47*pi/2)≠ 0) : -1/tan(47*pi/2)=1 / tan(137*pi/2):=
begin
have : -(1 / tan(47 * pi / 2)) = -1/tan(47*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(61*pi) = 1 / tan(47*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (61*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = -tan(61*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = 1 / tan(137*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_74_test : 1 - 2*sin(361*pi/12)**2=2 * sin(pi/3) * cos(pi/3):=
begin
have : cos(361*pi/6) = 1 - 2 * sin(361*pi/12) ** 2,
{
have : cos(361*pi/6) = cos(2*(361*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(361*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_75_test : cos(-2*pi) - cos(pi)=-sin(307*pi/2) + sin(309*pi/2):=
begin
have : (-2) * (-sin(309 * pi / 2) / 2 + sin(307 * pi / 2) / 2) = -sin(307*pi/2) + sin(309*pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) * cos(154*pi) = -sin(309*pi/2) / 2 + sin(307*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((154*pi) + (-pi/2)) = sin(307*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((154*pi) - (-pi/2)) = sin(309*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : -2*(sin(-pi/2) * cos(154*pi)) = -2*sin(-pi/2)*cos(154*pi),
{
ring,
},
conv {to_rhs, rw this,},
have : (-2) * cos(154 * pi) * sin(-pi / 2) = -2*sin(-pi/2)*cos(154*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/2) = cos(154*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/2) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) - cos(pi) = - 2 * sin(-3*pi/2) * sin(-pi/2),
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
rw this,
end


lemma Trigo_76_test : sin(2113*pi/6)=1 / 2:=
begin
have : - -sin(2113 * pi / 6) = sin(2113*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(548*pi/3) = -sin(2113*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (548*pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(548*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (91),
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


lemma Trigo_77_test : cos(pi/3)*cos(433*pi/3) + sin(pi/3)*cos(-pi/6)=1:=
begin
have : - -cos(433 * pi / 3) * cos(pi / 3) + sin(pi / 3) * cos(-pi / 6) = cos(pi/3)*cos(433*pi/3) + sin(pi/3)*cos(-pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(433*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) * cos(-pi / 6) - sin(-pi / 6) * cos(pi / 3) = -sin(-pi/6)*cos(pi/3) + sin(pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(pi/3) * cos(-pi/6) - sin(-pi/6) * cos(pi/3),
{
have : sin(pi/2) = sin((pi/3) - (-pi/6)),
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


lemma Trigo_78_test (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : -sin(pi/12)*sin(pi/3)/(2*cos(pi/6)) + cos(pi/12)*cos(pi/6)=sqrt( 2 ) / 2:=
begin
have : -sin(pi / 12) * (sin(pi / 3) / (2 * cos(pi / 6))) + cos(pi / 12) * cos(pi / 6) = -sin(pi/12)*sin(pi/3)/(2*cos(pi/6)) + cos(pi/12)*cos(pi/6),
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
have : cos(pi/4) = -sin(pi/12) * sin(pi/6) + cos(pi/12) * cos(pi/6),
{
have : cos(pi/4) = cos((pi/12) + (pi/6)),
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


lemma Trigo_79_test : -32*sin(pi/12)**3*cos(pi/12)**3 + 6*sin(pi/12)*cos(pi/12)=- sin(83*pi/2):=
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
have : sin(pi/2) = - sin(83*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_80_test : cos(251*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos(251 * pi / 6) = cos(251*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(427*pi/6) = -cos(251*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (427*pi/6) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(427*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (35),
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


lemma Trigo_81_test : 4*sin(pi/12)**2*cos(pi/12)**2=1 - (cos(pi/3)*cos(pi/2) + sin(pi/3)*sin(pi/2))**2:=
begin
have : (2 * sin(pi / 12) * cos(pi / 12)) ** 2 = 4*sin(pi/12)**2*cos(pi/12)**2,
{
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
have : 1 - (sin(pi / 2) * sin(pi / 3) + cos(pi / 2) * cos(pi / 3)) ** 2 = 1 - (cos(pi/3)*cos(pi/2) + sin(pi/3)*sin(pi/2))**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(pi/2) * sin(pi/3) + cos(pi/2) * cos(pi/3),
{
have : cos(pi/6) = cos((pi/2) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 - cos(pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_82_test : sin(2*pi) * sin(-pi/2)=sin(48*pi)/2 - cos(153*pi/2)/2:=
begin
have : -cos(153 * pi / 2) / 2 + sin(48 * pi) / 2 = sin(48*pi)/2 - cos(153*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/2) = sin(48*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/2) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5 * pi / 2) / 2 - cos(153 * pi / 2) / 2 = -cos(153*pi/2)/2 + cos(5*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/2) = cos(153*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (3*pi/2) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * sin(-pi/2) = cos(5*pi/2) / 2 - cos(3*pi/2) / 2,
{
rw sin_mul_sin,
have : cos((2*pi) + (-pi/2)) = cos(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi) - (-pi/2)) = cos(5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_83_test : sin(-pi/3) ** 2=1 - sin(163*pi/6)**2:=
begin
have : cos(154*pi/3) = sin(163*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (154*pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - (-cos(154 * pi / 3)) ** 2 = 1 - cos(154*pi/3)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -cos(154*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (25),
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


lemma Trigo_84_test : -sin(11*pi/6)=1 / 2:=
begin
have : sin(1021*pi/6) = -sin(11*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (1021*pi/6) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(1021*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (85),
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


lemma Trigo_85_test (h0 : cos(pi/3)≠ 0) : (-sin(-pi/2)*sin(-pi/6) + cos(-pi/2)*cos(-pi/6))*sin(pi) + sin(-2*pi/3)*cos(pi)=sin(2*pi/3) / ( 2 * cos(pi/3) ):=
begin
have : sin(pi) * (-sin(-pi / 6) * sin(-pi / 2) + cos(-pi / 6) * cos(-pi / 2)) + sin((-2) * pi / 3) * cos(pi) = (-sin(-pi/2)*sin(-pi/6) + cos(-pi/2)*cos(-pi/6))*sin(pi) + sin(-2*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = -sin(-pi/6) * sin(-pi/2) + cos(-pi/6) * cos(-pi/2),
{
have : cos(-2*pi/3) = cos((-pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_86_test (h0 : cos(pi)≠ 0) (h1 : (cos(-pi)*cos(2*pi)-sin(-pi)*sin(2*pi))≠ 0) (h2 : (-sin(2*pi)*sin(-pi)+cos(2*pi)*cos(-pi))≠ 0) : sin(pi)/(cos(-pi)*cos(2*pi) - sin(-pi)*sin(2*pi))=1 / tan(143*pi/2):=
begin
have : sin(pi) / (-sin(2 * pi) * sin(-pi) + cos(2 * pi) * cos(-pi)) = sin(pi)/(cos(-pi)*cos(2*pi) - sin(-pi)*sin(2*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(2*pi) * sin(-pi) + cos(2*pi) * cos(-pi),
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
conv {to_lhs, rw ← this,},
have : tan(pi) = sin(pi) / cos(pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(143*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_87_test (h0 : cos(5*pi/6)≠ 0) (h1 : (2*cos(5*pi/6))≠ 0) (h2 : (2*(cos(-2*pi)*cos(17*pi/6)-sin(-2*pi)*sin(17*pi/6)))≠ 0) (h3 : (2*(-sin(17*pi/6)*sin((-2)*pi)+cos(17*pi/6)*cos((-2)*pi)))≠ 0) : sin(5*pi/3)/(2*(cos(-2*pi)*cos(17*pi/6) - sin(-2*pi)*sin(17*pi/6)))=1 / 2:=
begin
have : sin(5 * pi / 3) / (2 * (-sin(17 * pi / 6) * sin((-2) * pi) + cos(17 * pi / 6) * cos((-2) * pi))) = sin(5*pi/3)/(2*(cos(-2*pi)*cos(17*pi/6) - sin(-2*pi)*sin(17*pi/6))),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(17*pi/6) * sin(-2*pi) + cos(17*pi/6) * cos(-2*pi),
{
have : cos(5*pi/6) = cos((17*pi/6) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_88_test : -sin(-2*pi)*cos(106*pi) - sin(106*pi)*cos(-2*pi)=- sin(129*pi):=
begin
have : -(sin(106 * pi) * cos((-2) * pi) + sin((-2) * pi) * cos(106 * pi)) = -sin(-2*pi)*cos(106*pi) - sin(106*pi)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(104*pi) = sin(106*pi) * cos(-2*pi) + sin(-2*pi) * cos(106*pi),
{
have : sin(104*pi) = sin((106*pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(104*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - sin(129*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_89_test (h0 : cos(pi)≠ 0) (h1 : (-3*cos(pi/3)+4*cos(pi/3)**3)≠ 0) (h2 : (4*cos(pi/3)**3-3*cos(pi/3))≠ 0) : sin(pi)/(-3*cos(pi/3) + 4*cos(pi/3)**3)=0:=
begin
have : sin(pi) / (4 * cos(pi / 3) ** 3 - 3 * cos(pi / 3)) = sin(pi)/(-3*cos(pi/3) + 4*cos(pi/3)**3),
{
field_simp at *,
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


lemma Trigo_90_test (h0 : sin(pi/3)≠ 0) (h1 : (4*sin(pi/3)**2)≠ 0) (h2 : (2*sin(pi/3))≠ 0) : sin(263*pi/3)**2/(4*sin(pi/3)**2) + sin(pi/3)**2=1:=
begin
have : (-sin(263 * pi / 3)) ** 2 / (4 * sin(pi / 3) ** 2) + sin(pi / 3) ** 2 = sin(263*pi/3)**2/(4*sin(pi/3)**2) + sin(pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(263*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) ** 2 + (sin(2 * pi / 3) / (2 * sin(pi / 3))) ** 2 = sin(2*pi/3)**2/(4*sin(pi/3)**2) + sin(pi/3)**2,
{
field_simp at *,
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
have : sin(pi/3) ** 2 + cos(pi/3) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_91_test : -sin(175*pi)=cos(53*pi/2):=
begin
have : cos(117*pi/2) = sin(175*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (117*pi/2) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(117*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(53*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_92_test : 1 - 2*sin(361*pi/6)**2=1 / 2:=
begin
have : cos(361*pi/3) = 1 - 2 * sin(361*pi/6) ** 2,
{
have : cos(361*pi/3) = cos(2*(361*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(361*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (60),
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


lemma Trigo_93_test : -1 + 2*cos(30*pi)**2=- cos(153*pi):=
begin
have : 2 * cos(30 * pi) ** 2 - 1 = -1 + 2*cos(30*pi)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(60*pi) = 2 * cos(30*pi) ** 2 - 1,
{
have : cos(60*pi) = cos(2*(30*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(60*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = - cos(153*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_94_test : sin(-pi/3) + sin(-pi/3)*cos(pi/2) + sin(pi/2)*cos(-pi/3)=sin(-pi/3) + sin(pi/6):=
begin
have : sin(pi / 2) * cos(-pi / 3) + sin(-pi / 3) * cos(pi / 2) + sin(-pi / 3) = sin(-pi/3) + sin(-pi/3)*cos(pi/2) + sin(pi/2)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : 2 * (sin(-pi / 3) / 2 + sin(pi / 6) / 2) = sin(-pi/3) + sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/12) * cos(pi/4) = sin(-pi/3) / 2 + sin(pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-pi/12) + (pi/4)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/12) - (pi/4)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-pi/12) * cos(pi/4)) = 2*sin(-pi/12)*cos(pi/4),
{
ring,
},
conv {to_rhs, rw this,},
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


lemma Trigo_95_test (h0 : sin(563*pi/6)≠ 0) (h1 : (2*sin(563*pi/6))≠ 0) : sin(563*pi/3)/(2*sin(563*pi/6))=sqrt( 3 ) / 2:=
begin
have : cos(563*pi/6) = sin(563*pi/3) / ( 2 * sin(563*pi/6) ),
{
have : sin(563*pi/3) = sin(2*(563*pi/6)),
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
have : sin(2*pi/3) = cos(563*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (47),
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


lemma Trigo_96_test : sin(167*pi)=-cos(197*pi/2):=
begin
have : cos(107*pi/2) = -cos(197*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (107*pi/2) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(167*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(107*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_97_test (h0 : cos(pi/2)≠ 0) : -(sin(67*pi/2)*cos(2*pi) - sin(2*pi)*cos(67*pi/2))/cos(pi/2)=tan(pi/2):=
begin
have : sin(63*pi/2) = sin(67*pi/2) * cos(2*pi) - sin(2*pi) * cos(67*pi/2),
{
have : sin(63*pi/2) = sin((67*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(63*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (16),
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


lemma Trigo_98_test : cos(154*pi/3)=- 1 / 2:=
begin
have : sin(727*pi/6) = cos(154*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (727*pi/6) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(727*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (60),
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


lemma Trigo_99_test : -sin(-337*pi/4)=sqrt( 2 ) / 2:=
begin
have : -sin((-337) * pi / 4) = -sin(-337*pi/4),
{
field_simp at *,
},
have : cos(463*pi/4) = -sin(-337*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (463*pi/4) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = cos(463*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (58),
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


lemma Trigo_100_test : 1 - 2*sin(pi/4)**2=-sin(183*pi):=
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
have : sin(78*pi) = -sin(183*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (78*pi) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(78*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_101_test : -1 + 2*sin(149*pi/4)**2=- sin(138*pi):=
begin
have : -(1 - 2 * sin(149 * pi / 4) ** 2) = -1 + 2*sin(149*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(149*pi/2) = 1 - 2 * sin(149*pi/4) ** 2,
{
have : cos(149*pi/2) = cos(2*(149*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(149*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(138*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_102_test : -cos(67*pi/2)=2*sin(137*pi/2)*cos(pi/2):=
begin
have : sin(pi/2) = sin(137*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -cos(67*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (16),
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


lemma Trigo_103_test : -sin(-pi/2)*sin(509*pi/3) - cos(-pi/2)*cos(509*pi/3)=sin(-pi) * cos(pi/3) + sin(pi/3) * cos(-pi):=
begin
have : -(sin(509 * pi / 3) * sin(-pi / 2) + cos(509 * pi / 3) * cos(-pi / 2)) = -sin(-pi/2)*sin(509*pi/3) - cos(-pi/2)*cos(509*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1021*pi/6) = sin(509*pi/3) * sin(-pi/2) + cos(509*pi/3) * cos(-pi/2),
{
have : cos(1021*pi/6) = cos((509*pi/3) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = -cos(1021*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = sin(-pi) * cos(pi/3) + sin(pi/3) * cos(-pi),
{
have : sin(-2*pi/3) = sin((-pi) + (pi/3)),
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


lemma Trigo_104_test : -cos(1145*pi/6)=-cos(1135*pi/6):=
begin
have : sin(440*pi/3) = -cos(1135*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (440*pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -cos(1145*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(440*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_105_test : sin(-pi/2) + sin(-pi/6)*cos(-pi/2) - sin(-pi/2)*cos(395*pi/6)=2 * sin(-pi/12) * cos(-5*pi/12):=
begin
have : cos(-pi/6) = cos(395*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) - (sin(-pi / 2) * cos(-pi / 6) - sin(-pi / 6) * cos(-pi / 2)) = sin(-pi/2) + sin(-pi/6)*cos(-pi/2) - sin(-pi/2)*cos(-pi/6),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-pi/2) * cos(-pi/6) - sin(-pi/6) * cos(-pi/2),
{
have : sin(-pi/3) = sin((-pi/2) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) - sin(-pi/3) = 2 * sin(-pi/12) * cos(-5*pi/12),
{
rw sin_sub_sin,
have : cos(((-pi/2) + (-pi/3))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (-pi/3))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_106_test : cos(347*pi/2)=-sin(18*pi):=
begin
have : sin(-pi) = cos(347*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/2) = sin(18*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(13*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_107_test : -sin(-pi)*cos(-pi/2) + sin(259*pi/2)*cos(-pi)=cos(0):=
begin
have : sin(-pi/2) = sin(259*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (64),
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
have : sin(pi/2) = cos(0),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (0),
focus{repeat {apply congr_arg _}},
simp,
},
rw this,
end


lemma Trigo_108_test : ((sin(pi)*sin(4*pi/3) + cos(pi)*cos(4*pi/3))*cos(-pi/6) - sin(-pi/6)*sin(pi/3))**2=cos(pi/3) / 2 + 1 / 2:=
begin
have : (cos(-pi / 6) * (sin(4 * pi / 3) * sin(pi) + cos(4 * pi / 3) * cos(pi)) - sin(-pi / 6) * sin(pi / 3)) ** 2 = ((sin(pi)*sin(4*pi/3) + cos(pi)*cos(4*pi/3))*cos(-pi/6) - sin(-pi/6)*sin(pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(4*pi/3) * sin(pi) + cos(4*pi/3) * cos(pi),
{
have : cos(pi/3) = cos((4*pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(-pi / 6) * sin(pi / 3) + cos(-pi / 6) * cos(pi / 3)) ** 2 = (cos(-pi/6)*cos(pi/3) - sin(-pi/6)*sin(pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(-pi/6) * sin(pi/3) + cos(-pi/6) * cos(pi/3),
{
have : cos(pi/6) = cos((-pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_109_test (h0 : tan(977*pi/12)≠ 0) : 1/tan(977*pi/12)=2 - sqrt( 3 ):=
begin
have : -((-1) / tan(977 * pi / 12)) = 1/tan(977*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(731*pi/12) = -1 / tan(977*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (731*pi/12) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(731*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (61),
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


lemma Trigo_110_test : 2*sin(160*pi/3)*cos(pi/3)*cos(160*pi/3)=cos(-pi/2) / 2 + cos(pi/6) / 2:=
begin
have : 2 * sin(160 * pi / 3) * cos(160 * pi / 3) * cos(pi / 3) = 2*sin(160*pi/3)*cos(pi/3)*cos(160*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(320*pi/3) = 2 * sin(160*pi/3) * cos(160*pi/3),
{
have : sin(320*pi/3) = sin(2*(160*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(320*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) * cos(pi/3) = cos(-pi/2) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (pi/3)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (pi/3)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_111_test : -sin(195*pi/4)**2 + cos(195*pi/4)**2=0:=
begin
have : cos(195*pi/2) = -sin(195*pi/4) ** 2 + cos(195*pi/4) ** 2,
{
have : cos(195*pi/2) = cos(2*(195*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(195*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (49),
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


lemma Trigo_112_test : tan(413*pi/4)=1:=
begin
have : tan(105*pi/4) = tan(413*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (105*pi/4) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = tan(105*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (pi/4) (26),
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


lemma Trigo_113_test (h0 : -cos(511*pi/6)≠ 0) (h1 : cos(511*pi/6)≠ 0) : tan(pi/6)=-(-sin(-pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi))/cos(511*pi/6):=
begin
have : -(sin((-5) * pi / 6) * cos(-pi) - sin(-pi) * cos((-5) * pi / 6)) / cos(511 * pi / 6) = -(-sin(-pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi))/cos(511*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi / 6) / -cos(511 * pi / 6) = -sin(pi/6)/cos(511*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -cos(511*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (42),
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


lemma Trigo_114_test : sin(pi)*sin(137*pi/6) + cos(pi)*cos(137*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(137 * pi / 6) * sin(pi) + cos(137 * pi / 6) * cos(pi) = sin(pi)*sin(137*pi/6) + cos(pi)*cos(137*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(131*pi/6) = sin(137*pi/6) * sin(pi) + cos(137*pi/6) * cos(pi),
{
have : cos(131*pi/6) = cos((137*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(131*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (11),
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


lemma Trigo_115_test (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) (h2 : cos(1105*pi/6)≠ 0) : (1 - cos(2*pi/3))/cos(1105*pi/6)=sqrt( 3 ):=
begin
have : sin(2*pi/3) = cos(1105*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (91),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_116_test : sin(99*pi/2)=- 1:=
begin
have : - -sin(99 * pi / 2) = sin(99*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(32*pi) = -sin(99*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (32*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(32*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (15),
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


lemma Trigo_117_test : cos(-3*pi)*cos(-2*pi) + sin(-3*pi)*sin(-2*pi)=1 - 2*sin(245*pi/2)**2:=
begin
have : sin((-3) * pi) * sin((-2) * pi) + cos((-3) * pi) * cos((-2) * pi) = cos(-3*pi)*cos(-2*pi) + sin(-3*pi)*sin(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(-3*pi) * sin(-2*pi) + cos(-3*pi) * cos(-2*pi),
{
have : cos(-pi) = cos((-3*pi) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (-sin(245 * pi / 2)) ** 2 = 1 - 2*sin(245*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -sin(245*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (61),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_118_test : sin(pi)*sin(151*pi/3) + cos(2*pi/3)*cos(pi)=- sin(-pi/6) ** 2 + cos(-pi/6) ** 2:=
begin
have : sin(151 * pi / 3) * sin(pi) + cos(2 * pi / 3) * cos(pi) = sin(pi)*sin(151*pi/3) + cos(2*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(151*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(2*pi/3) * sin(pi) + cos(2*pi/3) * cos(pi),
{
have : cos(-pi/3) = cos((2*pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
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


lemma Trigo_119_test : -cos(239*pi/12)**2 + sin(239*pi/12)**2=- sqrt( 3 ) / 2:=
begin
have : -(-sin(239 * pi / 12) ** 2 + cos(239 * pi / 12) ** 2) = -cos(239*pi/12)**2 + sin(239*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(239*pi/6) = -sin(239*pi/12) ** 2 + cos(239*pi/12) ** 2,
{
have : cos(239*pi/6) = cos(2*(239*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -cos(239*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/6) (19),
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


lemma Trigo_120_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : cos(53*pi/2)/(2*cos(pi/2))=sin(373*pi/2):=
begin
have : sin(pi) = cos(53*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (12),
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
have : sin(pi/2) = sin(373*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_121_test : -1 + 2*(1 - 2*sin(pi/8)**2)**2=0:=
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


lemma Trigo_122_test : (-3*cos(pi/18) + 4*cos(pi/18)**3)*sin(-pi/3) - sin(pi/6)*cos(-pi/3)=sin(pi/2) * cos(-pi) + sin(-pi) * cos(pi/2):=
begin
have : sin(-pi / 3) * (4 * cos(pi / 18) ** 3 - 3 * cos(pi / 18)) - sin(pi / 6) * cos(-pi / 3) = (-3*cos(pi/18) + 4*cos(pi/18)**3)*sin(-pi/3) - sin(pi/6)*cos(-pi/3),
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
have : sin(-pi/2) = sin(-pi/3) * cos(pi/6) - sin(pi/6) * cos(-pi/3),
{
have : sin(-pi/2) = sin((-pi/3) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(pi/2) * cos(-pi) + sin(-pi) * cos(pi/2),
{
have : sin(-pi/2) = sin((pi/2) + (-pi)),
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


lemma Trigo_123_test (h0 : cos((pi/2)/2)≠ 0) (h1 : (1+cos(pi/2))≠ 0) (h2 : (cos(pi/2)+1)≠ 0) : -cos(85*pi)/(cos(pi/2) + 1)=1:=
begin
have : sin(pi/2) = -cos(85*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (42),
focus{repeat {apply congr_arg _}},
simp,
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
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_124_test : -1 + 2*sin(25*pi/4)**2=- cos(75*pi/2):=
begin
have : -(1 - 2 * sin(25 * pi / 4) ** 2) = -1 + 2*sin(25*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -cos(25*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(75*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_125_test : -1 + 2*cos(-pi/12)**2=(-sin(pi/3)*cos(pi/2) + sin(pi/2)*cos(pi/3))*sin(pi/3) + cos(pi/6)*cos(pi/3):=
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
have : (sin(pi / 2) * cos(pi / 3) - sin(pi / 3) * cos(pi / 2)) * sin(pi / 3) + cos(pi / 6) * cos(pi / 3) = (-sin(pi/3)*cos(pi/2) + sin(pi/2)*cos(pi/3))*sin(pi/3) + cos(pi/6)*cos(pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_126_test (h0 : cos(581*pi/6)≠ 0) : -sin(581*pi/6)/cos(581*pi/6)=tan(499*pi/6):=
begin
have : -(sin(581 * pi / 6) / cos(581 * pi / 6)) = -sin(581*pi/6)/cos(581*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(581*pi/6) = sin(581*pi/6) / cos(581*pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(581*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(499*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_127_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) : (-3*cos(pi/9) + 4*cos(pi/9)**3)*sin(pi/3)/(2*sin(pi/6))=cos(pi/6) / 2 + cos(pi/2) / 2:=
begin
have : ((-3) * cos(pi / 9) + 4 * cos(pi / 9) ** 3) * (sin(pi / 3) / (2 * sin(pi / 6))) = (-3*cos(pi/9) + 4*cos(pi/9)**3)*sin(pi/3)/(2*sin(pi/6)),
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
have : (4 * cos(pi / 9) ** 3 - 3 * cos(pi / 9)) * cos(pi / 6) = (-3*cos(pi/9) + 4*cos(pi/9)**3)*cos(pi/6),
{
field_simp at *,
repeat {left},
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
have : cos(pi/3) * cos(pi/6) = cos(pi/6) / 2 + cos(pi/2) / 2,
{
rw cos_mul_cos,
have : cos((pi/3) + (pi/6)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (pi/6)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_128_test : -cos(1365*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(653*pi/4) = cos(1365*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (653*pi/4) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(653*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/4) (81),
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


lemma Trigo_129_test (h0 : tan(85*pi/2)≠ 0) (h1 : tan(177*pi/2)≠ 0) : sin(-pi) / cos(-pi)=-1/tan(177*pi/2):=
begin
have : (-1) / tan(177 * pi / 2) = -1/tan(177*pi/2),
{
field_simp at *,
},
have : tan(85*pi/2) = tan(177*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (85*pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-1) / tan(85 * pi / 2) = -1/tan(85*pi/2),
{
field_simp at *,
},
have : tan(-pi) = -1 / tan(85*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) / cos(-pi) = tan(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_130_test : -cos(335*pi/2) + sin(2*pi)=-sin(-2*pi) + sin(pi):=
begin
have : sin(pi) = -cos(335*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi) + sin(2*pi) = 2 * sin(3*pi/2) * cos(-pi/2),
{
rw sin_add_sin,
have : sin(((pi) + (2*pi))/2) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (2*pi))/2) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_131_test : -sin(67*pi/2)=-cos(237*pi/2)**2 + cos(2*pi)**2:=
begin
have : cos(4*pi) = -sin(67*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(-cos(237 * pi / 2)) ** 2 + cos(2 * pi) ** 2 = -cos(237*pi/2)**2 + cos(2*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -cos(237*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (58),
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


lemma Trigo_132_test : -1 + 2*sin(556*pi/3)**2=1 / 2:=
begin
have : -1 + 2 * (-sin(556 * pi / 3)) ** 2 = -1 + 2*sin(556*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(556*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (92),
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


lemma Trigo_133_test (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) (h2 : cos(817*pi/6)≠ 0) : (1 - cos(2*pi/3))/cos(817*pi/6)=sqrt( 3 ):=
begin
have : sin(2*pi/3) = cos(817*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (67),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_134_test : sin(5*pi/6)*cos(pi/2) + sin(3*pi/2)*cos(5*pi/6)=sin(151*pi/3):=
begin
have : sin(5 * pi / 6) * cos(pi / 2) - -sin(3 * pi / 2) * cos(5 * pi / 6) = sin(5*pi/6)*cos(pi/2) + sin(3*pi/2)*cos(5*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(3*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(5*pi/6) * cos(pi/2) - sin(pi/2) * cos(5*pi/6),
{
have : sin(pi/3) = sin((5*pi/6) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(151*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_135_test : 3*cos(103*pi/36) - 4*cos(103*pi/36)**3=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(4 * cos(103 * pi / 36) ** 3 - 3 * cos(103 * pi / 36)) = 3*cos(103*pi/36) - 4*cos(103*pi/36)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(103*pi/12) = 4 * cos(103*pi/36) ** 3 - 3 * cos(103*pi/36),
{
have : cos(103*pi/12) = cos(3*(103*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(103*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/12) (4),
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


lemma Trigo_136_test (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : -cos(533*pi/6)=cos(11*pi/6)/(2*cos(pi/3)):=
begin
have : sin(2*pi/3) = cos(11*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = -cos(533*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (44),
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


lemma Trigo_137_test (h0 : cos(pi)≠ 0) (h1 : (1-tan(pi)**2)≠ 0) (h2 : cos((2*pi)/2)≠ 0) (h3 : (1-(sin(2*pi)/(1+cos(2*pi)))**2)≠ 0) (h4 : ((1+cos(2*pi))*(-sin(2*pi)**2/(1+cos(2*pi))**2+1))≠ 0) (h5 : (1+cos(2*pi))≠ 0) : 2*sin(2*pi)/((1 + cos(2*pi))*(-sin(2*pi)**2/(1 + cos(2*pi))**2 + 1))=- tan(71*pi):=
begin
have : 2 * (sin(2 * pi) / (1 + cos(2 * pi))) / (1 - (sin(2 * pi) / (1 + cos(2 * pi))) ** 2) = 2*sin(2*pi)/((1 + cos(2*pi))*(-sin(2*pi)**2/(1 + cos(2*pi))**2 + 1)),
{
field_simp at *,
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
have : tan(2*pi) = - tan(71*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_138_test : sin(pi/6)=sin(-2*pi)*sin(238*pi/3) - sin(297*pi/2)*cos(238*pi/3):=
begin
have : sin((-2) * pi) * sin(238 * pi / 3) - sin(297 * pi / 2) * cos(238 * pi / 3) = sin(-2*pi)*sin(238*pi/3) - sin(297*pi/2)*cos(238*pi/3),
{
field_simp at *,
},
have : cos(-2*pi) = sin(297*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(-sin(238 * pi / 3) * sin((-2) * pi) + cos(238 * pi / 3) * cos((-2) * pi)) = sin(-2*pi)*sin(238*pi/3) - cos(-2*pi)*cos(238*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(232*pi/3) = -sin(238*pi/3) * sin(-2*pi) + cos(238*pi/3) * cos(-2*pi),
{
have : cos(232*pi/3) = cos((238*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(232*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_139_test : sin(315*pi/2)=4 * cos(-pi) ** 3 - 3 * cos(-pi):=
begin
have : cos(79*pi) = sin(315*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (79*pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi) = cos(79*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-3*pi) (41),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_140_test (h0 : cos(pi/2)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan(pi/2)*tan(-pi/2))≠ 0) (h3 : (tan(-pi/2)*tan(pi/2)+1)≠ 0) (h4 : (tan(-pi/2)*tan(195*pi/2)+1)≠ 0) (h5 : (1+tan(-pi/2)*tan(195*pi/2))≠ 0) : (tan(195*pi/2) - tan(-pi/2))/(1 + tan(-pi/2)*tan(195*pi/2))=0:=
begin
have : (-tan(-pi / 2) + tan(195 * pi / 2)) / (tan(-pi / 2) * tan(195 * pi / 2) + 1) = (tan(195*pi/2) - tan(-pi/2))/(1 + tan(-pi/2)*tan(195*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = tan(195*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 2) - tan(-pi / 2)) / (1 + tan(pi / 2) * tan(-pi / 2)) = (-tan(-pi/2) + tan(pi/2))/(tan(-pi/2)*tan(pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(pi/2) - tan(-pi/2) ) / ( 1 + tan(pi/2) * tan(-pi/2) ),
{
have : tan(pi) = tan((pi/2) - (-pi/2)),
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


lemma Trigo_141_test : -2*sin(317*pi/4)*cos(317*pi/4)=sin(159*pi/2):=
begin
have : -(2 * sin(317 * pi / 4) * cos(317 * pi / 4)) = -2*sin(317*pi/4)*cos(317*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(317*pi/2) = 2 * sin(317*pi/4) * cos(317*pi/4),
{
have : sin(317*pi/2) = sin(2*(317*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(317*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(159*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_142_test : sin(pi/6)**2 + cos(365*pi/6)**2=1:=
begin
have : cos(535*pi/6) = cos(365*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (535*pi/6) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) ** 2 + (-cos(535 * pi / 6)) ** 2 = sin(pi/6)**2 + cos(535*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(535*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 + cos(pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_143_test (h0 : tan(33*pi/4)≠ 0) (h1 : cos((33*pi/2)/2)≠ 0) (h2 : sin(33*pi/2)≠ 0) (h3 : (sin(33*pi/2)/(1+cos(33*pi/2)))≠ 0) (h4 : (1+cos(33*pi/2))≠ 0) : (cos(33*pi/2) + 1)/sin(33*pi/2)=1:=
begin
have : 1 / (sin(33 * pi / 2) / (1 + cos(33 * pi / 2))) = (cos(33*pi/2) + 1)/sin(33*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(33*pi/4) = sin(33*pi/2) / ( 1 + cos(33*pi/2) ),
{
have : tan(33*pi/4) = tan((33*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = 1 / tan(33*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/4) (8),
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


lemma Trigo_144_test : 1 - 2*sin(551*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/24) = sin(551*pi/24),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/24) (11),
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


lemma Trigo_145_test : sin(2*pi/3)=-sin(-pi)*sin(721*pi/6) - sin(-pi/3)*sin(141*pi/2):=
begin
have : cos(-pi/3) = sin(721*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 3) * -sin(141 * pi / 2) - sin(-pi) * cos(-pi / 3) = -sin(-pi)*cos(-pi/3) - sin(-pi/3)*sin(141*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -sin(141*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_146_test (h0 : tan(929*pi/12)≠ 0) (h1 : cos((929*pi/6)/2)≠ 0) (h2 : (1+cos(929*pi/6))≠ 0) (h3 : sin(929*pi/6)≠ 0) (h4 : (sin(929*pi/6)/(1+cos(929*pi/6)))≠ 0) : (cos(929*pi/6) + 1)/sin(929*pi/6)=2 - sqrt( 3 ):=
begin
have : 1 / (sin(929 * pi / 6) / (1 + cos(929 * pi / 6))) = (cos(929*pi/6) + 1)/sin(929*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(929*pi/12) = sin(929*pi/6) / ( 1 + cos(929*pi/6) ),
{
have : tan(929*pi/12) = tan((929*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 1 / tan(929*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (77),
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


lemma Trigo_147_test : -cos(134*pi)=cos(-pi)*cos(120*pi) + sin(-pi)*cos(pi/2):=
begin
have : cos(120 * pi) * cos(-pi) + sin(-pi) * cos(pi / 2) = cos(-pi)*cos(120*pi) + sin(-pi)*cos(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = cos(120*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -cos(134*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(pi/2) * cos(-pi) + sin(-pi) * cos(pi/2),
{
have : sin(-pi/2) = sin((pi/2) + (-pi)),
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


lemma Trigo_148_test : cos(-3*pi/2)*cos(pi/2) + sin(pi/2)*sin(225*pi/2)=- sin(271*pi/2):=
begin
have : cos((-3) * pi / 2) * cos(pi / 2) + sin(225 * pi / 2) * sin(pi / 2) = cos(-3*pi/2)*cos(pi/2) + sin(pi/2)*sin(225*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2) = sin(225*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-3*pi/2) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-3) * pi / 2) * sin(pi / 2) + cos((-3) * pi / 2) * cos(pi / 2) = cos(-3*pi/2)*cos(pi/2) + sin(-3*pi/2)*sin(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - sin(271*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_149_test : -sin(26*pi)=-sin(3*pi):=
begin
have : cos(59*pi/2) = sin(3*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (59*pi/2) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -sin(26*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(59*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_150_test : -sin(pi)*sin(97*pi/2) + sin(-3*pi)*cos(pi)=sin(65*pi):=
begin
have : sin(pi) * -sin(97 * pi / 2) + sin((-3) * pi) * cos(pi) = -sin(pi)*sin(97*pi/2) + sin(-3*pi)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi) = -sin(97*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-3) * pi) * cos(pi) + sin(pi) * cos((-3) * pi) = sin(pi)*cos(-3*pi) + sin(-3*pi)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-3*pi) * cos(pi) + sin(pi) * cos(-3*pi),
{
have : sin(-2*pi) = sin((-3*pi) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(65*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_151_test : -4*sin(-pi/2)**2*cos(-pi/2)**2 + cos(-pi)**2=sin(165*pi/2):=
begin
have : -(2 * sin(-pi / 2) * cos(-pi / 2)) ** 2 + cos(-pi) ** 2 = -4*sin(-pi/2)**2*cos(-pi/2)**2 + cos(-pi)**2,
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
have : cos(-2*pi) = sin(165*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_152_test (h0 : tan(517*pi/6)≠ 0) (h1 : -tan((-127)*pi/6)≠ 0) (h2 : tan(-127*pi/6)≠ 0) : -1/tan(-127*pi/6)=sqrt( 3 ):=
begin
have : 1 / -tan((-127) * pi / 6) = -1/tan(-127*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(517*pi/6) = -tan(-127*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (517*pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_153_test : cos(pi/2) + cos(-pi/3)=2 * cos(-pi/12) * cos(-5*pi/12):=
begin
have : 2 * (cos(pi / 2) / 2 + cos(-pi / 3) / 2) = cos(pi/2) + cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) * cos(-5*pi/12) = cos(pi/2) / 2 + cos(-pi/3) / 2,
{
rw cos_mul_cos,
have : cos((pi/12) + (-5*pi/12)) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/12) - (-5*pi/12)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 2*(cos(pi/12) * cos(-5*pi/12)) = 2*cos(-5*pi/12)*cos(pi/12),
{
ring,
},
conv {to_lhs, rw this,},
have : 2 * cos(pi / 12) * cos((-5) * pi / 12) = 2*cos(-5*pi/12)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(-pi/2) = 2 * cos(pi/12) * cos(-5*pi/12),
{
rw cos_add_cos,
have : cos(((-pi/3) + (-pi/2))/2) = cos(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (-pi/2))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(-pi/3) + cos(-pi/2)) = cos(-pi/2)+cos(-pi/3),
{
ring,
},
conv {to_lhs, rw this,},
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


lemma Trigo_154_test : -sin(895*pi/6)*cos(pi) - sin(pi)*cos(895*pi/6)=- 1 / 2:=
begin
have : -(sin(895 * pi / 6) * cos(pi) + sin(pi) * cos(895 * pi / 6)) = -sin(895*pi/6)*cos(pi) - sin(pi)*cos(895*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(901*pi/6) = sin(895*pi/6) * cos(pi) + sin(pi) * cos(895*pi/6),
{
have : sin(901*pi/6) = sin((895*pi/6) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(901*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (74),
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




lemma Trigo_156_test : -sin(515*pi/12)**2 + cos(515*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : cos(515*pi/6) = -sin(515*pi/12) ** 2 + cos(515*pi/12) ** 2,
{
have : cos(515*pi/6) = cos(2*(515*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(515*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (42),
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


lemma Trigo_157_test (h0 : sin(287*pi/2)≠ 0) (h1 : (2*sin(287*pi/2))≠ 0) : -sin(287*pi)/(2*sin(287*pi/2))=- cos(21*pi/2):=
begin
have : -(sin(287 * pi) / (2 * sin(287 * pi / 2))) = -sin(287*pi)/(2*sin(287*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(287*pi/2) = sin(287*pi) / ( 2 * sin(287*pi/2) ),
{
have : sin(287*pi) = sin(2*(287*pi/2)),
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
have : sin(2*pi) = -cos(287*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = - cos(21*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_158_test (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) (h2 : cos(-2*pi)≠ 0) (h3 : (2*cos(-2*pi)**2)≠ 0) (h4 : (2*cos((-2)*pi))≠ 0) : sin(-4*pi)/(2*cos(-2*pi)**2)=1 / tan(35*pi/2):=
begin
have : sin((-4) * pi) / (2 * cos((-2) * pi)) / cos((-2) * pi) = sin(-4*pi)/(2*cos(-2*pi)**2),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin((-2) * pi) / cos((-2) * pi) = sin(-2*pi)/cos(-2*pi),
{
field_simp at *,
},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = 1 / tan(35*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-2*pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_159_test : cos(65*pi/2)**2=1 - cos(-2*pi) ** 2:=
begin
have : cos(239*pi/2) = cos(65*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (239*pi/2) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(239 * pi / 2)) ** 2 = cos(239*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -cos(239*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (58),
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


lemma Trigo_160_test : cos(-3*pi)*cos(2*pi) - 2*sin(-3*pi/2)*sin(2*pi)*cos(-3*pi/2)=sin(219*pi/2):=
begin
have : cos((-3) * pi) * cos(2 * pi) - 2 * sin((-3) * pi / 2) * cos((-3) * pi / 2) * sin(2 * pi) = cos(-3*pi)*cos(2*pi) - 2*sin(-3*pi/2)*sin(2*pi)*cos(-3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi) = 2 * sin(-3*pi/2) * cos(-3*pi/2),
{
have : sin(-3*pi) = sin(2*(-3*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : -sin((-3) * pi) * sin(2 * pi) + cos((-3) * pi) * cos(2 * pi) = cos(-3*pi)*cos(2*pi) - sin(-3*pi)*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(-3*pi) * sin(2*pi) + cos(-3*pi) * cos(2*pi),
{
have : cos(-pi) = cos((-3*pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(219*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_161_test : -sin(-pi/6)*cos(2*pi/3) - sin(47*pi/3)*cos(-pi/6)=1 / 2:=
begin
have : -sin(-pi / 6) * cos(2 * pi / 3) + -sin(47 * pi / 3) * cos(-pi / 6) = -sin(-pi/6)*cos(2*pi/3) - sin(47*pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(47*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi / 3) * cos(-pi / 6) - sin(-pi / 6) * cos(2 * pi / 3) = -sin(-pi/6)*cos(2*pi/3) + sin(2*pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(2*pi/3) * cos(-pi/6) - sin(-pi/6) * cos(2*pi/3),
{
have : sin(5*pi/6) = sin((2*pi/3) - (-pi/6)),
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


lemma Trigo_162_test (h0 : cos(11*pi/12)≠ 0) (h1 : cos(pi/6)≠ 0) (h2 : (1+tan(11*pi/12)*tan(pi/6))≠ 0) (h3 : (tan(pi/6)*tan(11*pi/12)+1)≠ 0) (h4 : (1/tan(85*pi/3)*tan(11*pi/12)+1)≠ 0) (h5 : tan(85*pi/3)≠ 0) (h6 : (tan(11*pi/12)/tan(85*pi/3)+1)≠ 0) : (-1/tan(85*pi/3) + tan(11*pi/12))/(tan(11*pi/12)/tan(85*pi/3) + 1)=- 1:=
begin
have : (-(1 / tan(85 * pi / 3)) + tan(11 * pi / 12)) / (1 / tan(85 * pi / 3) * tan(11 * pi / 12) + 1) = (-1/tan(85*pi/3) + tan(11*pi/12))/(tan(11*pi/12)/tan(85*pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(85*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(11 * pi / 12) - tan(pi / 6)) / (1 + tan(11 * pi / 12) * tan(pi / 6)) = (-tan(pi/6) + tan(11*pi/12))/(tan(pi/6)*tan(11*pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = ( tan(11*pi/12) - tan(pi/6) ) / ( 1 + tan(11*pi/12) * tan(pi/6) ),
{
have : tan(3*pi/4) = tan((11*pi/12) - (pi/6)),
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


lemma Trigo_163_test : (sin(pi/6)*cos(pi/3) + sin(265*pi/3)*cos(pi/6))**2=1 - cos(pi/2) ** 2:=
begin
have : sin(pi/3) = sin(265*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 3) * cos(pi / 6) + sin(pi / 6) * cos(pi / 3)) ** 2 = (sin(pi/6)*cos(pi/3) + sin(pi/3)*cos(pi/6))**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) ** 2 = 1 - cos(pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_164_test : -cos(104*pi/3)=sin(-pi/6)/2 + sin(5*pi/6)/2 + sin(pi/2)*cos(pi/3):=
begin
have : sin(pi/3) * cos(pi/2) = sin(-pi/6) / 2 + sin(5*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (pi/2)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (pi/2)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (sin(pi/3) * cos(pi/2)) = sin(pi/3)*cos(pi/2),
{
ring,
},
have : sin(5*pi/6) = -cos(104*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(pi/3) * cos(pi/2) + sin(pi/2) * cos(pi/3),
{
have : sin(5*pi/6) = sin((pi/3) + (pi/2)),
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


lemma Trigo_165_test : -sin(386*pi/3)=-sin(97*pi/2)*cos(-pi/6) + sin(-pi)*sin(-pi/6):=
begin
have : sin(-pi / 6) * sin(-pi) + cos(-pi / 6) * -sin(97 * pi / 2) = -sin(97*pi/2)*cos(-pi/6) + sin(-pi)*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -sin(97*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/6) = -sin(386*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_166_test (h0 : cos(3*pi/2)≠ 0) (h1 : (2*cos(3*pi/2))≠ 0) (h2 : (2*(-sin(-pi/2)*sin(2*pi)+cos(-pi/2)*cos(2*pi)))≠ 0) : sin(3*pi)/(2*(-sin(-pi/2)*sin(2*pi) + cos(-pi/2)*cos(2*pi)))=- 4 * sin(pi/2) ** 3 + 3 * sin(pi/2):=
begin
have : cos(3*pi/2) = -sin(-pi/2) * sin(2*pi) + cos(-pi/2) * cos(2*pi),
{
have : cos(3*pi/2) = cos((-pi/2) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_167_test : sin(-4*pi)=(-8*cos(187*pi/3)**3 + 6*cos(187*pi/3))*sin(-2*pi):=
begin
have : 2 * (4 * (-cos(187 * pi / 3)) ** 3 - 3 * -cos(187 * pi / 3)) * sin((-2) * pi) = (-8*cos(187*pi/3)**3 + 6*cos(187*pi/3))*sin(-2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) = -cos(187*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/3) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin((-2) * pi) * (4 * cos((-2) * pi / 3) ** 3 - 3 * cos((-2) * pi / 3)) = 2*(4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(-2*pi),
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


lemma Trigo_168_test : sin(5*pi/2)=sin(2*pi)*cos(-pi/2) - (-4*cos(193*pi/3)**3 + 3*cos(193*pi/3))*sin(-pi/2):=
begin
have : sin(2 * pi) * cos(-pi / 2) - (4 * (-cos(193 * pi / 3)) ** 3 - 3 * -cos(193 * pi / 3)) * sin(-pi / 2) = sin(2*pi)*cos(-pi/2) - (-4*cos(193*pi/3)**3 + 3*cos(193*pi/3))*sin(-pi/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/3) = -cos(193*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2 * pi) * cos(-pi / 2) - sin(-pi / 2) * (4 * cos(2 * pi / 3) ** 3 - 3 * cos(2 * pi / 3)) = sin(2*pi)*cos(-pi/2) - (4*cos(2*pi/3)**3 - 3*cos(2*pi/3))*sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(5*pi/2) = sin(2*pi) * cos(-pi/2) - sin(-pi/2) * cos(2*pi),
{
have : sin(5*pi/2) = sin((2*pi) - (-pi/2)),
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


lemma Trigo_169_test : -1 + 2*(sin(5*pi/3)*sin(2*pi) + cos(5*pi/3)*cos(2*pi))**2=- sin(-pi/3) ** 2 + cos(-pi/3) ** 2:=
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
have : 2 * cos(-pi / 3) ** 2 - 1 = -1 + 2*cos(-pi/3)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
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


lemma Trigo_170_test : sin(7*pi/12)*cos(-pi/2) + sin(-pi/2)*cos(2105*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(7*pi/12) = cos(2105*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (7*pi/12) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(7*pi/12) * cos(-pi/2) + sin(-pi/2) * cos(7*pi/12),
{
have : sin(pi/12) = sin((7*pi/12) + (-pi/2)),
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


lemma Trigo_171_test : sin(-pi) - sin(pi/6)=2*sin(-7*pi/12)*cos(-5*pi/12):=
begin
have : 2 * (-1 + 2 * (cos((-5) * pi / 12) / 2 + 1 / 2)) * sin((-7) * pi / 12) = 2*sin(-7*pi/12)*cos(-5*pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/24) ** 2 = cos(-5*pi/12) / 2 + 1 / 2,
{
have : cos(-5*pi/12) = cos(2*(-5*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin((-7) * pi / 12) * (2 * cos((-5) * pi / 24) ** 2 - 1) = 2*(-1 + 2*cos(-5*pi/24)**2)*sin(-7*pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/12) = 2 * cos(-5*pi/24) ** 2 - 1,
{
have : cos(-5*pi/12) = cos(2*(-5*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_172_test : -sin(pi/2)*sin(73*pi)=-sin(-2*pi)*sin(-pi/2):=
begin
have : -sin(73 * pi) * sin(pi / 2) = -sin(pi/2)*sin(73*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(73*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 * ((-2) * sin(-pi / 2) * sin((-2) * pi)) = -sin(-2*pi)*sin(-pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/2) - cos(-3*pi/2) = -2 * sin(-pi/2) * sin(-2*pi),
{
rw cos_sub_cos,
have : sin(((-5*pi/2) + (-3*pi/2))/2) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-5*pi/2) - (-3*pi/2))/2) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 1/2*(cos(-5*pi/2) - cos(-3*pi/2)) = cos(-5*pi/2)/2-cos(-3*pi/2)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-2*pi) * sin(pi/2) = cos(-5*pi/2) / 2 - cos(-3*pi/2) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_173_test : 2*(cos(-pi/8)*cos(pi/2) - sin(-pi/8)*sin(pi/2))*sin(3*pi/8)=sqrt( 2 ) / 2:=
begin
have : 2 * sin(3 * pi / 8) * (-sin(-pi / 8) * sin(pi / 2) + cos(-pi / 8) * cos(pi / 2)) = 2*(cos(-pi/8)*cos(pi/2) - sin(-pi/8)*sin(pi/2))*sin(3*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = -sin(-pi/8) * sin(pi/2) + cos(-pi/8) * cos(pi/2),
{
have : cos(3*pi/8) = cos((-pi/8) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_174_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) (h2 : (2*sin(499*pi/6))≠ 0) (h3 : (2*-sin(499*pi/6))≠ 0) : -sin(pi/3)/(2*sin(499*pi/6))=sin(164*pi/3):=
begin
have : sin(pi / 3) / (2 * -sin(499 * pi / 6)) = -sin(pi/3)/(2*sin(499*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(499*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (41),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi/6) = sin(164*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_175_test (h0 : cos(-2*pi)≠ 0) (h1 : (2*cos(-2*pi))≠ 0) (h2 : (2*cos((-2)*pi))≠ 0) : sin(-4*pi)*cos(17*pi/6)/(2*cos(-2*pi)) + sin(17*pi/6)*cos(-2*pi)=1 / 2:=
begin
have : sin((-4) * pi) / (2 * cos((-2) * pi)) * cos(17 * pi / 6) + sin(17 * pi / 6) * cos((-2) * pi) = sin(-4*pi)*cos(17*pi/6)/(2*cos(-2*pi)) + sin(17*pi/6)*cos(-2*pi),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(17 * pi / 6) * cos((-2) * pi) + sin((-2) * pi) * cos(17 * pi / 6) = sin(-2*pi)*cos(17*pi/6) + sin(17*pi/6)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(17*pi/6) * cos(-2*pi) + sin(-2*pi) * cos(17*pi/6),
{
have : sin(5*pi/6) = sin((17*pi/6) + (-2*pi)),
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




lemma Trigo_177_test : -1 + 2*cos(349*pi/6)**2=2 * cos(pi/6) ** 2 - 1:=
begin
have : 2 * cos(349 * pi / 6) ** 2 - 1 = -1 + 2*cos(349*pi/6)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(349*pi/3) = 2 * cos(349*pi/6) ** 2 - 1,
{
have : cos(349*pi/3) = cos(2*(349*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(349*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (58),
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


lemma Trigo_178_test (h0 : tan(271*pi/6)≠ 0) (h1 : cos((271*pi/3)/2)≠ 0) (h2 : (1-cos(271*pi/3))≠ 0) (h3 : sin(271*pi/3)≠ 0) (h4 : ((1-cos(271*pi/3))/sin(271*pi/3))≠ 0) : -sin(271*pi/3)/(1 - cos(271*pi/3))=- sqrt( 3 ):=
begin
have : (-1) / ((1 - cos(271 * pi / 3)) / sin(271 * pi / 3)) = -sin(271*pi/3)/(1 - cos(271*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(271*pi/6) = ( 1 - cos(271*pi/3) ) / sin(271*pi/3),
{
have : tan(271*pi/6) = tan((271*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(271 * pi / 6) = -1/tan(271*pi/6),
{
field_simp at *,
},
have : tan(2*pi/3) = -1 / tan(271*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi/3) (44),
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


lemma Trigo_179_test : sin(pi/6)*cos(359*pi/6) - sin(359*pi/6)*cos(pi/6)=sin(260*pi/3):=
begin
have : -(sin(359 * pi / 6) * cos(pi / 6) - sin(pi / 6) * cos(359 * pi / 6)) = sin(pi/6)*cos(359*pi/6) - sin(359*pi/6)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(179*pi/3) = sin(359*pi/6) * cos(pi/6) - sin(pi/6) * cos(359*pi/6),
{
have : sin(179*pi/3) = sin((359*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(179*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(260*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_180_test (h0 : cos(143*pi/2)≠ 0) (h1 : (2*cos(143*pi/2))≠ 0) : -sin(143*pi)/(2*cos(143*pi/2))=1:=
begin
have : -(sin(143 * pi) / (2 * cos(143 * pi / 2))) = -sin(143*pi)/(2*cos(143*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(143*pi/2) = sin(143*pi) / ( 2 * cos(143*pi/2) ),
{
have : sin(143*pi) = sin(2*(143*pi/2)),
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
have : sin(pi/2) = -sin(143*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (36),
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




lemma Trigo_182_test (h0 : tan(155*pi/2)≠ 0) (h1 : cos(155*pi/4)≠ 0) (h2 : (1-tan(155*pi/4)**2)≠ 0) (h3 : (2*tan(155*pi/4)/(1-tan(155*pi/4)**2))≠ 0) (h4 : (2*tan(155*pi/4))≠ 0) : (1 - tan(155*pi/4)**2)/(2*tan(155*pi/4))=- 1 / tan(185*pi/2):=
begin
have : 1 / (2 * tan(155 * pi / 4) / (1 - tan(155 * pi / 4) ** 2)) = (1 - tan(155*pi/4)**2)/(2*tan(155*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(155*pi/2) = 2 * tan(155*pi/4) / ( 1 - tan(155*pi/4) ** 2 ),
{
have : tan(155*pi/2) = tan(2*(155*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = 1 / tan(155*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - 1 / tan(185*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_183_test (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/6)≠ 0) (h2 : (2*cos(-pi/6)**2)≠ 0) (h3 : (2*cos(-pi/6))≠ 0) : sin(-pi/3)/(2*cos(-pi/6)**2)=- 1 / tan(187*pi/3):=
begin
have : sin(-pi / 3) / (2 * cos(-pi / 6)) / cos(-pi / 6) = sin(-pi/3)/(2*cos(-pi/6)**2),
{
field_simp at *,
repeat {left},
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
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - 1 / tan(187*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_184_test : -2*sin(pi/4)**2 + cos(pi/6)*cos(5*pi/6) - sin(pi/6)*sin(5*pi/6) + 1=2 * cos(pi/4) * cos(3*pi/4):=
begin
have : cos(pi / 6) * cos(5 * pi / 6) - sin(pi / 6) * sin(5 * pi / 6) + (1 - 2 * sin(pi / 4) ** 2) = -2*sin(pi/4)**2 + cos(pi/6)*cos(5*pi/6) - sin(pi/6)*sin(5*pi/6) + 1,
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
have : -sin(5 * pi / 6) * sin(pi / 6) + cos(5 * pi / 6) * cos(pi / 6) + cos(pi / 2) = cos(pi/6)*cos(5*pi/6) - sin(pi/6)*sin(5*pi/6) + cos(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(5*pi/6) * sin(pi/6) + cos(5*pi/6) * cos(pi/6),
{
have : cos(pi) = cos((5*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) + cos(pi/2) = 2 * cos(pi/4) * cos(3*pi/4),
{
rw cos_add_cos,
have : cos(((pi) + (pi/2))/2) = cos(3*pi/4),
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
ring,
},
rw this,
end


lemma Trigo_185_test : cos(74*pi)**2=1 - sin(103*pi)**2:=
begin
have : cos(-2*pi) = cos(74*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(103*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (50),
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


lemma Trigo_186_test (h0 : tan(296*pi/3)≠ 0) (h1 : tan(533*pi/3)≠ 0) : -1/tan(533*pi/3)=tan(559*pi/6):=
begin
have : (-1) / tan(533 * pi / 3) = -1/tan(533*pi/3),
{
field_simp at *,
},
have : tan(296*pi/3) = tan(533*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (296*pi/3) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(296 * pi / 3) = -1/tan(296*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(296*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(559*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_187_test : cos(1121*pi/3)=1 / 2:=
begin
have : sin(1081*pi/6) = cos(1121*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1081*pi/6) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(1081*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (90),
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


lemma Trigo_188_test : -3*sin(97*pi/2) + 4*sin(97*pi/2)**3=cos(68*pi):=
begin
have : -((-4) * sin(97 * pi / 2) ** 3 + 3 * sin(97 * pi / 2)) = -3*sin(97*pi/2) + 4*sin(97*pi/2)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(291*pi/2) = -4 * sin(97*pi/2) ** 3 + 3 * sin(97*pi/2),
{
have : sin(291*pi/2) = sin(3*(97*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(291*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(68*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_189_test : -sin(-pi)*cos(442*pi/3) + sin(442*pi/3)*cos(-pi)=- sin(83*pi/3):=
begin
have : sin(442 * pi / 3) * cos(-pi) - sin(-pi) * cos(442 * pi / 3) = -sin(-pi)*cos(442*pi/3) + sin(442*pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(445*pi/3) = sin(442*pi/3) * cos(-pi) - sin(-pi) * cos(442*pi/3),
{
have : sin(445*pi/3) = sin((442*pi/3) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(445*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - sin(83*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_190_test (h0 : sin(103*pi/2)≠ 0) (h1 : (2*sin(103*pi/2))≠ 0) : -cos(343*pi/2)=-sin(103*pi)/(2*sin(103*pi/2)):=
begin
have : sin(2*pi) = -cos(343*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(103 * pi) / (2 * sin(103 * pi / 2))) = -sin(103*pi)/(2*sin(103*pi/2)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(103*pi/2) = sin(103*pi) / ( 2 * sin(103*pi/2) ),
{
have : sin(103*pi) = sin(2*(103*pi/2)),
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
have : sin(2*pi) = - cos(103*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_191_test : sin(pi)=-3*cos(299*pi/6) + 4*cos(299*pi/6)**3:=
begin
have : (-3) * cos(299 * pi / 6) + 4 * cos(299 * pi / 6) ** 3 = -3*cos(299*pi/6) + 4*cos(299*pi/6)**3,
{
field_simp at *,
},
have : cos(119*pi/6) = cos(299*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (119*pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 4 * cos(119 * pi / 6) ** 3 - 3 * cos(119 * pi / 6) = -3*cos(119*pi/6) + 4*cos(119*pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(119*pi/2) = 4 * cos(119*pi/6) ** 3 - 3 * cos(119*pi/6),
{
have : cos(119*pi/2) = cos(3*(119*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = cos(119*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_193_test : sin(2*pi/3)*cos(pi/2) - sin(pi/2)*cos(2*pi/3)=-sin(1127*pi/6):=
begin
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
have : cos(526*pi/3) = sin(1127*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (526*pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(526*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_194_test : 2*sin(277*pi/12)*cos(277*pi/12)=sin(1117*pi/6):=
begin
have : sin(277*pi/6) = 2 * sin(277*pi/12) * cos(277*pi/12),
{
have : sin(277*pi/6) = sin(2*(277*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(277*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(1117*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_195_test (h0 : tan(95*pi/3)≠ 0) (h1 : cos((190*pi/3)/2)≠ 0) (h2 : sin(190*pi/3)≠ 0) (h3 : (1+cos(190*pi/3))≠ 0) (h4 : (sin(190*pi/3)/(1+cos(190*pi/3)))≠ 0) : -(cos(190*pi/3) + 1)/sin(190*pi/3)=- 1 / tan(245*pi/3):=
begin
have : (-1) / (sin(190 * pi / 3) / (1 + cos(190 * pi / 3))) = -(cos(190*pi/3) + 1)/sin(190*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(95*pi/3) = sin(190*pi/3) / ( 1 + cos(190*pi/3) ),
{
have : tan(95*pi/3) = tan((190*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(95 * pi / 3) = -1/tan(95*pi/3),
{
field_simp at *,
},
have : tan(pi/6) = -1 / tan(95*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = - 1 / tan(245*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/6) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_196_test : cos(-4*pi)=-(sin(-pi)/2 - sin(2*pi)/2 - sin(pi/2)*cos(-3*pi/2))**2 + cos(-2*pi)**2:=
begin
have : -(-sin(2 * pi) / 2 + sin(-pi) / 2 - sin(pi / 2) * cos((-3) * pi / 2)) ** 2 + cos((-2) * pi) ** 2 = -(sin(-pi)/2 - sin(2*pi)/2 - sin(pi/2)*cos(-3*pi/2))**2 + cos(-2*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/2) * cos(pi/2) = -sin(2*pi) / 2 + sin(-pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/2) + (-3*pi/2)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (-3*pi/2)) = sin(2*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : (sin(-3*pi/2) * cos(pi/2)) = sin(-3*pi/2)*cos(pi/2),
{
ring,
},
have : -(sin((-3) * pi / 2) * cos(pi / 2) - sin(pi / 2) * cos((-3) * pi / 2)) ** 2 + cos((-2) * pi) ** 2 = -(sin(-3*pi/2)*cos(pi/2) - sin(pi/2)*cos(-3*pi/2))**2 + cos(-2*pi)**2,
{
field_simp at *,
},
have : sin(-2*pi) = sin(-3*pi/2) * cos(pi/2) - sin(pi/2) * cos(-3*pi/2),
{
have : sin(-2*pi) = sin((-3*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
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


lemma Trigo_197_test : cos(657*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -cos(657 * pi / 4) = cos(657*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(27*pi/4) = -cos(657*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (27*pi/4) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(27*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/4) (3),
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


lemma Trigo_198_test (h0 : (2*cos(-pi/12)**2-1)≠ 0) (h1 : (-1+2*cos(-pi/12)**2)≠ 0) (h2 : cos((-pi/3)/2)≠ 0) (h3 : sin(-pi/3)≠ 0) : (1 - cos(-pi/3))/sin(-pi/3)=sin(-pi/6)/(-1 + 2*cos(-pi/12)**2):=
begin
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
have : sin(-pi / 6) / (2 * cos(-pi / 12) ** 2 - 1) = sin(-pi/6)/(-1 + 2*cos(-pi/12)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_199_test (h0 : sin(pi/3)≠ 0) (h1 : (2*sin(pi/3))≠ 0) (h2 : (2*cos(383*pi/6))≠ 0) : sin(2*pi/3)/(2*cos(383*pi/6))=1 / 2:=
begin
have : sin(pi/3) = cos(383*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (31),
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


lemma Trigo_200_test : cos(-pi/6)=-2*sin(512*pi/3)*cos(512*pi/3):=
begin
have : -(2 * sin(512 * pi / 3) * cos(512 * pi / 3)) = -2*sin(512*pi/3)*cos(512*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(1024*pi/3) = 2 * sin(512*pi/3) * cos(512*pi/3),
{
have : sin(1024*pi/3) = sin(2*(512*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(574*pi/3) = sin(1024*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (574*pi/3) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(574*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_201_test : (-4*sin(pi/9)**3 + 3*sin(pi/9))*sin(-pi/2)=cos(-5*pi/6)/2 + sin(-pi/3)*sin(pi/6)/2 - cos(-pi/3)*cos(pi/6)/2:=
begin
have : sin(-pi / 2) * ((-4) * sin(pi / 9) ** 3 + 3 * sin(pi / 9)) = (-4*sin(pi/9)**3 + 3*sin(pi/9))*sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos((-5) * pi / 6) / 2 - (-sin(pi / 6) * sin(-pi / 3) + cos(pi / 6) * cos(-pi / 3)) / 2 = cos(-5*pi/6)/2 + sin(-pi/3)*sin(pi/6)/2 - cos(-pi/3)*cos(pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(pi/6) * sin(-pi/3) + cos(pi/6) * cos(-pi/3),
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
conv {to_rhs, rw ← this,},
have : sin(-pi/2) * sin(pi/3) = cos(-5*pi/6) / 2 - cos(-pi/6) / 2,
{
rw sin_mul_sin,
have : cos((-pi/2) + (pi/3)) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (pi/3)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_203_test : sin(-pi/6)*cos(95*pi/6) + cos(-pi/6)*cos(pi/3)=- cos(49*pi/2):=
begin
have : sin(pi/3) = cos(95*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(-pi/6) * sin(pi/3) + cos(-pi/6) * cos(pi/3),
{
have : cos(-pi/2) = cos((-pi/6) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(49*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_204_test (h0 : tan(595*pi/12)≠ 0) (h1 : cos(589*pi/12)≠ 0) (h2 : cos(-pi/2)≠ 0) (h3 : ((tan(589*pi/12)-tan(-pi/2))/(1+tan(589*pi/12)*tan(-pi/2)))≠ 0) (h4 : (tan(589*pi/12)-tan(-pi/2))≠ 0) (h5 : (1+tan(589*pi/12)*tan(-pi/2))≠ 0) : -(tan(-pi/2)*tan(589*pi/12) + 1)/(tan(589*pi/12) - tan(-pi/2))=2 - sqrt( 3 ):=
begin
have : (-1) / ((tan(589 * pi / 12) - tan(-pi / 2)) / (1 + tan(589 * pi / 12) * tan(-pi / 2))) = -(tan(-pi/2)*tan(589*pi/12) + 1)/(tan(589*pi/12) - tan(-pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(595*pi/12) = ( tan(589*pi/12) - tan(-pi/2) ) / ( 1 + tan(589*pi/12) * tan(-pi/2) ),
{
have : tan(595*pi/12) = tan((589*pi/12) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(595 * pi / 12) = -1/tan(595*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(595*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (49),
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


lemma Trigo_205_test : -1 + 2*cos(751*pi/12)**2=cos(125*pi/6):=
begin
have : 2 * cos(751 * pi / 12) ** 2 - 1 = -1 + 2*cos(751*pi/12)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(751*pi/6) = 2 * cos(751*pi/12) ** 2 - 1,
{
have : cos(751*pi/6) = cos(2*(751*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(751*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(125*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_206_test : -(-sin(125*pi/4)**2 + cos(125*pi/4)**2)*cos(pi)=- sin(-pi) / 2 + sin(3*pi) / 2:=
begin
have : -cos(pi) * (-sin(125 * pi / 4) ** 2 + cos(125 * pi / 4) ** 2) = -(-sin(125*pi/4)**2 + cos(125*pi/4)**2)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(125*pi/2) = -sin(125*pi/4) ** 2 + cos(125*pi/4) ** 2,
{
have : cos(125*pi/2) = cos(2*(125*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(125 * pi / 2) * cos(pi) = -cos(pi)*cos(125*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(125*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(pi) = - sin(-pi) / 2 + sin(3*pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi) + (2*pi)) = sin(3*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (2*pi)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_207_test (h0 : cos((-pi/3)/2)≠ 0) (h1 : sin(-pi/3)≠ 0) (h2 : sin(160*pi/3)≠ 0) : (1 - cos(-pi/3))/sin(160*pi/3)=tan(143*pi/6):=
begin
have : sin(-pi/3) = sin(160*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (26),
focus{repeat {apply congr_arg _}},
simp,
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
have : tan(-pi/6) = tan(143*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-pi/6) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_208_test : (-4*sin(3*pi/4)**3 + 3*sin(3*pi/4))*sin(2*pi) + cos(2*pi)*cos(9*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(2 * pi) * ((-4) * sin(3 * pi / 4) ** 3 + 3 * sin(3 * pi / 4)) + cos(2 * pi) * cos(9 * pi / 4) = (-4*sin(3*pi/4)**3 + 3*sin(3*pi/4))*sin(2*pi) + cos(2*pi)*cos(9*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(9*pi/4) = -4 * sin(3*pi/4) ** 3 + 3 * sin(3*pi/4),
{
have : sin(9*pi/4) = sin(3*(3*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(9 * pi / 4) * sin(2 * pi) + cos(9 * pi / 4) * cos(2 * pi) = sin(2*pi)*sin(9*pi/4) + cos(2*pi)*cos(9*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(9*pi/4) * sin(2*pi) + cos(9*pi/4) * cos(2*pi),
{
have : cos(pi/4) = cos((9*pi/4) - (2*pi)),
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


lemma Trigo_209_test : sin(-pi)*sin(649*pi/4) - cos(-pi)*cos(649*pi/4)=sqrt( 2 ) / 2:=
begin
have : -(-sin(649 * pi / 4) * sin(-pi) + cos(649 * pi / 4) * cos(-pi)) = sin(-pi)*sin(649*pi/4) - cos(-pi)*cos(649*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(645*pi/4) = -sin(649*pi/4) * sin(-pi) + cos(649*pi/4) * cos(-pi),
{
have : cos(645*pi/4) = cos((649*pi/4) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(645*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (80),
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


lemma Trigo_210_test : sin(119*pi/2)**2=1 - cos(291*pi/2)**2:=
begin
have : (-sin(119 * pi / 2)) ** 2 = sin(119*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(119*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(291*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) ** 2 = 1 - cos(pi/2) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_211_test (h0 : cos((pi/2)/2)≠ 0) (h1 : (1+cos(pi/2))≠ 0) (h2 : (cos(pi/2)+1)≠ 0) : -sin(195*pi/2)/(cos(pi/2) + 1)=1:=
begin
have : sin(pi/2) = -sin(195*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (48),
focus{repeat {apply congr_arg _}},
simp,
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
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_212_test : -cos(-140*pi/3)=1 / 2:=
begin
have : -cos((-140) * pi / 3) = -cos(-140*pi/3),
{
field_simp at *,
},
have : cos(260*pi/3) = cos(-140*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (260*pi/3) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = -cos(260*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (43),
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


lemma Trigo_213_test : sin(307*pi/2)=-cos(194*pi):=
begin
have : cos(52*pi) = cos(194*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (52*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(307*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(52*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_214_test : sin(-81*pi/2)=cos(35*pi):=
begin
have : - -sin((-81) * pi / 2) = sin(-81*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(198*pi) = -sin(-81*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (198*pi) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -cos(198*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(35*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_215_test (h0 : tan(83*pi/2)≠ 0) (h1 : cos(88*pi)≠ 0) : -1/tan(83*pi/2)=sin(-2*pi)/cos(88*pi):=
begin
have : sin((-2) * pi) / cos(88 * pi) = sin(-2*pi)/cos(88*pi),
{
field_simp at *,
},
have : cos(-2*pi) = cos(88*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-1) / tan(83 * pi / 2) = -1/tan(83*pi/2),
{
field_simp at *,
},
have : tan(-2*pi) = -1 / tan(83*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-2*pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_216_test (h0 : sin(5*pi/6)≠ 0) (h1 : (2*sin(5*pi/6))≠ 0) (h2 : (4*sin(5*pi/6))≠ 0) : sin(pi/2) * sin(-pi/3)=-cos(995*pi/6)/2 + sin(5*pi/3)/(4*sin(5*pi/6)):=
begin
have : cos(pi/6) = cos(995*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5 * pi / 3) / (2 * sin(5 * pi / 6)) / 2 - cos(pi / 6) / 2 = -cos(pi/6)/2 + sin(5*pi/3)/(4*sin(5*pi/6)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/6) = sin(5*pi/3) / ( 2 * sin(5*pi/6) ),
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
conv {to_rhs, rw ← this,},
have : sin(pi/2) * sin(-pi/3) = cos(5*pi/6) / 2 - cos(pi/6) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_217_test : -cos(103*pi/3)=cos(274*pi/3):=
begin
have : sin(299*pi/6) = cos(274*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (299*pi/6) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = -cos(103*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(299*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_218_test : (-sin(-4*pi/3)*sin(pi/3) + (1 - 2*sin(-2*pi/3)**2)*cos(pi/3))**2=cos(-2*pi) / 2 + 1 / 2:=
begin
have : (-sin((-4) * pi / 3) * sin(pi / 3) + (1 - 2 * sin((-2) * pi / 3) ** 2) * cos(pi / 3)) ** 2 = (-sin(-4*pi/3)*sin(pi/3) + (1 - 2*sin(-2*pi/3)**2)*cos(pi/3))**2,
{
field_simp at *,
},
have : cos(-4*pi/3) = 1 - 2 * sin(-2*pi/3) ** 2,
{
have : cos(-4*pi/3) = cos(2*(-2*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : (-sin((-4) * pi / 3) * sin(pi / 3) + cos((-4) * pi / 3) * cos(pi / 3)) ** 2 = (-sin(-4*pi/3)*sin(pi/3) + cos(-4*pi/3)*cos(pi/3))**2,
{
field_simp at *,
},
have : cos(-pi) = -sin(-4*pi/3) * sin(pi/3) + cos(-4*pi/3) * cos(pi/3),
{
have : cos(-pi) = cos((-4*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_219_test (h0 : cos((pi/6)/2)≠ 0) (h1 : (cos(pi/6)+1)≠ 0) (h2 : (1+cos(pi/6))≠ 0) : sin(1057*pi/6)/(cos(pi/6) + 1)=2 - sqrt( 3 ):=
begin
have : sin(pi/6) = sin(1057*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_220_test (h0 : sin(pi/3)≠ 0) (h1 : (4*sin(pi/3)**2)≠ 0) (h2 : (2*sin(pi/3))≠ 0) : sin(2*pi/3)**2/(4*sin(pi/3)**2)=cos(pi/3)**2:=
begin
have : (2 * cos(pi / 3) ** 2 - 1) / 2 + 1 / 2 = cos(pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : (sin(2 * pi / 3) / (2 * sin(pi / 3))) ** 2 = sin(2*pi/3)**2/(4*sin(pi/3)**2),
{
field_simp at *,
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


lemma Trigo_221_test (h0 : cos(505*pi/24)≠ 0) (h1 : (1-tan(505*pi/24)**2)≠ 0) : 2*tan(505*pi/24)/(1 - tan(505*pi/24)**2)=2 - sqrt( 3 ):=
begin
have : tan(505*pi/12) = 2 * tan(505*pi/24) / ( 1 - tan(505*pi/24) ** 2 ),
{
have : tan(505*pi/12) = tan(2*(505*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = tan(505*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (42),
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


lemma Trigo_222_test : sin(331*pi/6)**2 + sin(58*pi/3)**2=1:=
begin
have : sin(331 * pi / 6) ** 2 + (-sin(58 * pi / 3)) ** 2 = sin(331*pi/6)**2 + sin(58*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(58*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(331 * pi / 6)) ** 2 + cos(pi / 6) ** 2 = sin(331*pi/6)**2 + cos(pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(331*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 + cos(pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_223_test : cos(343*pi/2)=-cos(469*pi/2):=
begin
have : cos(-pi/2) = cos(343*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(82*pi) = -cos(469*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (82*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(82*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_224_test : -3*sin(601*pi/12) + 4*sin(601*pi/12)**3=- sqrt( 2 ) / 2:=
begin
have : -((-4) * sin(601 * pi / 12) ** 3 + 3 * sin(601 * pi / 12)) = -3*sin(601*pi/12) + 4*sin(601*pi/12)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(601*pi/4) = -4 * sin(601*pi/12) ** 3 + 3 * sin(601*pi/12),
{
have : sin(601*pi/4) = sin(3*(601*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_225_test : -tan(-15*pi/4)=- 1:=
begin
have : -tan((-15) * pi / 4) = -tan(-15*pi/4),
{
field_simp at *,
},
have : tan(91*pi/4) = -tan(-15*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (91*pi/4) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = tan(91*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (3*pi/4) (22),
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


lemma Trigo_226_test : -sin(151*pi/2)**2 + cos(151*pi/2)**2 + cos(pi/3)=2 * cos(pi/3) * cos(2*pi/3):=
begin
have : cos(151*pi) = -sin(151*pi/2) ** 2 + cos(151*pi/2) ** 2,
{
have : cos(151*pi) = cos(2*(151*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(151*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) + cos(pi/3) = 2 * cos(pi/3) * cos(2*pi/3),
{
rw cos_add_cos,
have : cos(((pi) + (pi/3))/2) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (pi/3))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_227_test : cos(-pi/3)*cos(2*pi/3) - sin(-pi/3)*sin(2*pi/3)=cos(pi/3):=
begin
have : 2 * (cos(pi / 3) / 2 + 1 / 2) - 1 = cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : -sin(2 * pi / 3) * sin(-pi / 3) + cos(2 * pi / 3) * cos(-pi / 3) = cos(-pi/3)*cos(2*pi/3) - sin(-pi/3)*sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(2*pi/3) * sin(-pi/3) + cos(2*pi/3) * cos(-pi/3),
{
have : cos(pi/3) = cos((2*pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_228_test : -cos(49*pi)=1:=
begin
have : cos(65*pi) = cos(49*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (65*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(65*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (32),
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


lemma Trigo_229_test (h0 : sin(pi/2)≠ 0) : sin(326*pi)=sin(pi) / ( 2 * sin(pi/2) ):=
begin
have : - -sin(326 * pi) = sin(326*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(163*pi) = -sin(326*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (163*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(163*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (81),
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


lemma Trigo_230_test (h0 : cos(pi/6)≠ 0) (h1 : cos(pi/2)≠ 0) (h2 : cos(pi/3)≠ 0) (h3 : (1+tan(pi/3)*tan(pi/2))≠ 0) (h4 : (1+tan(pi/2)*tan(pi/3))≠ 0) : -sin(943*pi/6)/cos(pi/6)=(-tan(pi/3) + tan(pi/2))/(1 + tan(pi/3)*tan(pi/2)):=
begin
have : (tan(pi / 2) - tan(pi / 3)) / (1 + tan(pi / 2) * tan(pi / 3)) = (-tan(pi/3) + tan(pi/2))/(1 + tan(pi/3)*tan(pi/2)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(pi/6) = ( tan(pi/2) - tan(pi/3) ) / ( 1 + tan(pi/2) * tan(pi/3) ),
{
have : tan(pi/6) = tan((pi/2) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -sin(943*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (78),
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


lemma Trigo_231_test (h0 : cos(85*pi/2)≠ 0) (h1 : (2*cos(85*pi/2))≠ 0) : sin(85*pi)*cos(pi/3)/(2*cos(85*pi/2))=- sin(-pi/6) / 2 + sin(5*pi/6) / 2:=
begin
have : sin(85 * pi) / (2 * cos(85 * pi / 2)) * cos(pi / 3) = sin(85*pi)*cos(pi/3)/(2*cos(85*pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(85*pi/2) = sin(85*pi) / ( 2 * cos(85*pi/2) ),
{
have : sin(85*pi) = sin(2*(85*pi/2)),
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
have : sin(pi/2) = sin(85*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(pi/3) = - sin(-pi/6) / 2 + sin(5*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (pi/2)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (pi/2)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_232_test : -sin(607*pi/6)=1 / 2:=
begin
have : sin(275*pi/6) = sin(607*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (275*pi/6) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(275*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (22),
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


lemma Trigo_233_test (h0 : sin(15*pi)≠ 0) (h1 : (2*sin(15*pi))≠ 0) : -sin(30*pi)/(2*sin(15*pi))=cos(44*pi):=
begin
have : -(sin(30 * pi) / (2 * sin(15 * pi))) = -sin(30*pi)/(2*sin(15*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(15*pi) = sin(30*pi) / ( 2 * sin(15*pi) ),
{
have : sin(30*pi) = sin(2*(15*pi)),
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
have : cos(-2*pi) = -cos(15*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(44*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_234_test : -(cos(pi/6)*cos(pi/3) + sin(pi/6)*sin(pi/3))*sin(130*pi)=sin(-11*pi/6) / 2 + sin(-13*pi/6) / 2:=
begin
have : -sin(130 * pi) * (sin(pi / 6) * sin(pi / 3) + cos(pi / 6) * cos(pi / 3)) = -(cos(pi/6)*cos(pi/3) + sin(pi/6)*sin(pi/3))*sin(130*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(130*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/6) = sin(-11*pi/6) / 2 + sin(-13*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-pi/6)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-pi/6)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_235_test : -sin(pi)*cos(1259*pi/6)=cos(4*pi/3) / 2 - cos(2*pi/3) / 2:=
begin
have : sin(pi) * -cos(1259 * pi / 6) = -sin(pi)*cos(1259*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(256*pi/3) = -cos(1259*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (256*pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(256*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * sin(-pi/3) = cos(4*pi/3) / 2 - cos(2*pi/3) / 2,
{
rw sin_mul_sin,
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
rw this,
end


lemma Trigo_236_test : -cos(195*pi/2)=-3*sin(154*pi) + 4*sin(154*pi)**3:=
begin
have : (-4) * (-sin(154 * pi)) ** 3 + 3 * -sin(154 * pi) = -3*sin(154*pi) + 4*sin(154*pi)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = -sin(154*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-6*pi) = -cos(195*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-6*pi) (45),
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


lemma Trigo_237_test (h0 : cos(pi)≠ 0) (h1 : (-3*cos(pi/3)+4*cos(pi/3)**3)≠ 0) (h2 : (4*cos(pi/3)**3-3*cos(pi/3))≠ 0) : cos(61*pi/2)/(-3*cos(pi/3) + 4*cos(pi/3)**3)=tan(pi):=
begin
have : cos(61 * pi / 2) / (4 * cos(pi / 3) ** 3 - 3 * cos(pi / 3)) = cos(61*pi/2)/(-3*cos(pi/3) + 4*cos(pi/3)**3),
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
have : sin(pi) = cos(61*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) / cos(pi) = tan(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_238_test : -sin(pi)**2 + cos(pi)**2=sin(-pi/6)*cos(226*pi/3) - sin(226*pi/3)*cos(-pi/6):=
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
have : -(sin(226 * pi / 3) * cos(-pi / 6) - sin(-pi / 6) * cos(226 * pi / 3)) = sin(-pi/6)*cos(226*pi/3) - sin(226*pi/3)*cos(-pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(151*pi/2) = sin(226*pi/3) * cos(-pi/6) - sin(-pi/6) * cos(226*pi/3),
{
have : sin(151*pi/2) = sin((226*pi/3) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(151*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_239_test (h0 : cos(-pi)≠ 0) : tan(-pi)=(sin(-2*pi/3)*cos(-pi/3) + 2*sin(-pi/6)*cos(-2*pi/3)*cos(-pi/6))/cos(-pi):=
begin
have : (sin((-2) * pi / 3) * cos(-pi / 3) + 2 * sin(-pi / 6) * cos(-pi / 6) * cos((-2) * pi / 3)) / cos(-pi) = (sin(-2*pi/3)*cos(-pi/3) + 2*sin(-pi/6)*cos(-2*pi/3)*cos(-pi/6))/cos(-pi),
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
have : (sin((-2) * pi / 3) * cos(-pi / 3) + sin(-pi / 3) * cos((-2) * pi / 3)) / cos(-pi) = (sin(-2*pi/3)*cos(-pi/3) + sin(-pi/3)*cos(-2*pi/3))/cos(-pi),
{
field_simp at *,
},
have : sin(-pi) = sin(-2*pi/3) * cos(-pi/3) + sin(-pi/3) * cos(-2*pi/3),
{
have : sin(-pi) = sin((-2*pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi) = sin(-pi) / cos(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_240_test : -cos(28*pi/3)=1 / 2:=
begin
have : sin(325*pi/6) = -cos(28*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (325*pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(325*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (27),
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


lemma Trigo_241_test (h0 : cos(pi/3)≠ 0) (h1 : sin(913*pi/6)≠ 0) : sin(pi/3)/sin(913*pi/6)=sqrt( 3 ):=
begin
have : cos(pi/3) = sin(913*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (76),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_242_test : -sin(182*pi)=0:=
begin
have : cos(75*pi/2) = sin(182*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (75*pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(75*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (18),
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


lemma Trigo_243_test : -cos(-49*pi/6)=- sin(104*pi/3):=
begin
have : -cos((-49) * pi / 6) = -cos(-49*pi/6),
{
field_simp at *,
},
have : sin(392*pi/3) = cos(-49*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (392*pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(392*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(104*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_244_test : cos(243*pi)=- cos(94*pi):=
begin
have : cos(67*pi) = cos(243*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (67*pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(67*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(94*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_245_test : cos(245*pi/2)=sin(0)/2 - sin(2*pi)*cos(-2*pi) - sin(4*pi)/2:=
begin
have : sin(-4*pi) = cos(245*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-4*pi) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(4 * pi) / 2 + sin(0) / 2 - sin(2 * pi) * cos((-2) * pi) = sin(0)/2 - sin(2*pi)*cos(-2*pi) - sin(4*pi)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * cos(2*pi) = -sin(4*pi) / 2 + sin(0) / 2,
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
conv {to_rhs, rw ← this,},
have : (sin(-2*pi) * cos(2*pi)) = sin(-2*pi)*cos(2*pi),
{
ring,
},
have : sin(-4*pi) = sin(-2*pi) * cos(2*pi) - sin(2*pi) * cos(-2*pi),
{
have : sin(-4*pi) = sin((-2*pi) - (2*pi)),
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




lemma Trigo_247_test : -3*sin(1181*pi/6) + 4*sin(1181*pi/6)**3=cos(65*pi):=
begin
have : (-3) * sin(1181 * pi / 6) + 4 * sin(1181 * pi / 6) ** 3 = -3*sin(1181*pi/6) + 4*sin(1181*pi/6)**3,
{
field_simp at *,
},
have : cos(pi/3) = sin(1181*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (98),
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
have : cos(pi) = cos(65*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_248_test : -sin(419*pi/3)=sin(13*pi/3):=
begin
have : sin(pi/3) = -sin(419*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(13 * pi / 3) = sin(13*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(367*pi/6) = -sin(13*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (367*pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = - cos(367*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_249_test : 2*cos(71*pi/3)*cos(74*pi/3)=2 * cos(-pi/3) * cos(2*pi/3):=
begin
have : cos(145*pi/3) + cos(pi) = 2 * cos(71*pi/3) * cos(74*pi/3),
{
rw cos_add_cos,
have : cos(((145*pi/3) + (pi))/2) = cos(74*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((145*pi/3) - (pi))/2) = cos(71*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(145*pi/3) + cos(pi)) = cos(pi)+cos(145*pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(145 * pi / 3) + cos(pi) = cos(pi) + cos(145*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(145*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) + cos(pi) = 2 * cos(-pi/3) * cos(2*pi/3),
{
rw cos_add_cos,
have : cos(((pi/3) + (pi))/2) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (pi))/2) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_250_test : -tan(32*pi/3)=sqrt( 3 ):=
begin
have : tan(103*pi/3) = -tan(32*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (103*pi/3) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(103*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (34),
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


lemma Trigo_251_test : cos(pi/3) - cos(pi/2)=-2*sin(-689*pi/12)*sin(-pi/12):=
begin
have : (-2) * sin(-pi / 12) * sin((-689) * pi / 12) = -2*sin(-689*pi/12)*sin(-pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(1997*pi/12) = sin(-689*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (1997*pi/12) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-2) * sin(-pi / 12) * sin(1997 * pi / 12) = -2*sin(-pi/12)*sin(1997*pi/12),
{
field_simp at *,
},
have : sin(5*pi/12) = sin(1997*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi/12) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) - cos(pi/2) = - 2 * sin(-pi/12) * sin(5*pi/12),
{
rw cos_sub_cos,
have : sin(((pi/3) + (pi/2))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (pi/2))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_252_test : -4*cos(1721*pi/18)**3 + 3*cos(1721*pi/18)=sqrt( 3 ) / 2:=
begin
have : (-4) * cos(1721 * pi / 18) ** 3 + 3 * cos(1721 * pi / 18) = -4*cos(1721*pi/18)**3 + 3*cos(1721*pi/18),
{
field_simp at *,
},
have : sin(pi/9) = cos(1721*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (47),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_253_test : sin(92*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(455*pi/6) = sin(92*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (455*pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(455*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (37),
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


lemma Trigo_254_test : cos(95*pi)=1 - 2*sin(pi/2)**2:=
begin
have : cos(pi) = cos(95*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 2) ** 2 + (1 - sin(pi / 2) ** 2) = 1 - 2*sin(pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) ** 2 = 1 - sin(pi/2) ** 2,
{
rw cos_sq',
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


lemma Trigo_255_test : -sin(245*pi/3)=sin(578*pi/3):=
begin
have : cos(397*pi/6) = -sin(245*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (397*pi/6) (7),
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
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(578*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_256_test : -sin(83*pi/2)*cos(349*pi/2)=sin(-pi) / 2 + sin(0) / 2:=
begin
have : sin(83 * pi / 2) * -cos(349 * pi / 2) = -sin(83*pi/2)*cos(349*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(349*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(83*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (20),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_257_test (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : -cos(-2*pi) - cos(129*pi/2)/(2*sin(pi/2))=- 2 * sin(5*pi/4) * sin(-3*pi/4):=
begin
have : -cos((-2) * pi) + -cos(129 * pi / 2) / (2 * sin(pi / 2)) = -cos(-2*pi) - cos(129*pi/2)/(2*sin(pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -cos(129*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) / (2 * sin(pi / 2)) - cos((-2) * pi) = -cos(-2*pi) + sin(pi)/(2*sin(pi/2)),
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
have : cos(pi/2) - cos(-2*pi) = - 2 * sin(5*pi/4) * sin(-3*pi/4),
{
rw cos_sub_cos,
have : sin(((pi/2) + (-2*pi))/2) = sin(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (-2*pi))/2) = sin(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_258_test : sin(-7*pi/3)*cos(-2*pi) - sin(-2*pi)*cos(-7*pi/3)=sin(334*pi/3):=
begin
have : sin((-7) * pi / 3) * cos((-2) * pi) - sin((-2) * pi) * cos((-7) * pi / 3) = sin(-7*pi/3)*cos(-2*pi) - sin(-2*pi)*cos(-7*pi/3),
{
field_simp at *,
},
have : sin(-pi/3) = sin(-7*pi/3) * cos(-2*pi) - sin(-2*pi) * cos(-7*pi/3),
{
have : sin(-pi/3) = sin((-7*pi/3) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(641*pi/6) = sin(334*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (641*pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = cos(641*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_259_test (h0 : cos(pi/2)≠ 0) (h1 : (1-tan(pi/2)**2)≠ 0) (h2 : cos((pi)/2)≠ 0) (h3 : (cos(pi)+1)≠ 0) (h4 : (1+cos(pi))≠ 0) (h5 : ((-sin(pi)**2/(cos(pi)+1)**2+1)*(cos(pi)+1))≠ 0) (h6 : (1-(sin(pi)/(1+cos(pi)))**2)≠ 0) : 2*sin(pi)/((-sin(pi)**2/(cos(pi) + 1)**2 + 1)*(cos(pi) + 1))=tan(66*pi):=
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
have : tan(pi) = tan(66*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_260_test : -sin(-2*pi)*sin(5*pi/2) + (cos(-pi/3)*cos(17*pi/6) - sin(-pi/3)*sin(17*pi/6))*cos(-2*pi)=- cos(323*pi/2):=
begin
have : -sin((-2) * pi) * sin(5 * pi / 2) + cos((-2) * pi) * (-sin(17 * pi / 6) * sin(-pi / 3) + cos(17 * pi / 6) * cos(-pi / 3)) = -sin(-2*pi)*sin(5*pi/2) + (cos(-pi/3)*cos(17*pi/6) - sin(-pi/3)*sin(17*pi/6))*cos(-2*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/2) = -sin(17*pi/6) * sin(-pi/3) + cos(17*pi/6) * cos(-pi/3),
{
have : cos(5*pi/2) = cos((17*pi/6) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 2) * sin((-2) * pi) + cos(5 * pi / 2) * cos((-2) * pi) = -sin(-2*pi)*sin(5*pi/2) + cos(-2*pi)*cos(5*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(5*pi/2) * sin(-2*pi) + cos(5*pi/2) * cos(-2*pi),
{
have : cos(pi/2) = cos((5*pi/2) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(323*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_261_test : cos(pi/6)*cos(1003*pi/6) + sin(pi/6)*sin(1003*pi/6)=- cos(90*pi):=
begin
have : sin(1003 * pi / 6) * sin(pi / 6) + cos(1003 * pi / 6) * cos(pi / 6) = cos(pi/6)*cos(1003*pi/6) + sin(pi/6)*sin(1003*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(167*pi) = sin(1003*pi/6) * sin(pi/6) + cos(1003*pi/6) * cos(pi/6),
{
have : cos(167*pi) = cos((1003*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(167*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(90*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_262_test : 3*sin(pi/2)*cos(-5*pi/6) + 3*sin(-5*pi/6)*cos(pi/2) - 4*(sin(pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi/2))**3=- sin(85*pi):=
begin
have : 3 * (sin((-5) * pi / 6) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 6)) - 4 * (sin((-5) * pi / 6) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 6)) ** 3 = 3*sin(pi/2)*cos(-5*pi/6) + 3*sin(-5*pi/6)*cos(pi/2) - 4*(sin(pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi/2))**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-5*pi/6) * cos(pi/2) + sin(pi/2) * cos(-5*pi/6),
{
have : sin(-pi/3) = sin((-5*pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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
have : sin(-pi) = - sin(85*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_263_test (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) (h2 : cos((313*pi/3)/2)≠ 0) (h3 : ((1-cos(313*pi/3))/sin(313*pi/3))≠ 0) (h4 : sin(313*pi/3)≠ 0) (h5 : (1-cos(313*pi/3))≠ 0) : (1 - cos(2*pi/3))/sin(2*pi/3)=sin(313*pi/3)/(1 - cos(313*pi/3)):=
begin
have : 1 / ((1 - cos(313 * pi / 3)) / sin(313 * pi / 3)) = sin(313*pi/3)/(1 - cos(313*pi/3)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(313*pi/6) = ( 1 - cos(313*pi/3) ) / sin(313*pi/3),
{
have : tan(313*pi/6) = tan((313*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
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
have : tan(pi/3) = 1 / tan(313*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_264_test : -cos(736*pi/3)=1 / 2:=
begin
have : cos(256*pi/3) = cos(736*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (256*pi/3) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(256*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (42),
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


lemma Trigo_265_test (h0 : cos(64*pi)≠ 0) (h1 : (2*cos(64*pi))≠ 0) : cos(pi/2)=-sin(-118*pi)/(2*cos(64*pi)):=
begin
have : -sin((-118) * pi) / (2 * cos(64 * pi)) = -sin(-118*pi)/(2*cos(64*pi)),
{
field_simp at *,
},
have : sin(128*pi) = -sin(-118*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (128*pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(64*pi) = sin(128*pi) / ( 2 * cos(64*pi) ),
{
have : sin(128*pi) = sin(2*(64*pi)),
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
have : cos(pi/2) = sin(64*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_266_test : 4*sin(1583*pi/36)**3 - 3*sin(1583*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-4) * (-sin(1583 * pi / 36)) ** 3 + 3 * -sin(1583 * pi / 36) = 4*sin(1583*pi/36)**3 - 3*sin(1583*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) = -sin(1583*pi/36),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/36) (22),
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


lemma Trigo_267_test : -sin(323*pi)=0:=
begin
have : cos(305*pi/2) = sin(323*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (305*pi/2) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(305*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (76),
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


lemma Trigo_268_test : -sin(83*pi/3)=sin(457*pi/3):=
begin
have : cos(191*pi/6) = sin(457*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (191*pi/6) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(83*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(191*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_269_test (h0 : sin(3*pi/4)≠ 0) (h1 : (2*sin(3*pi/4))≠ 0) : (sin(5*pi/2)*cos(pi) - sin(pi)*cos(5*pi/2))/(2*sin(3*pi/4))=- sqrt( 2 ) / 2:=
begin
have : sin(3*pi/2) = sin(5*pi/2) * cos(pi) - sin(pi) * cos(5*pi/2),
{
have : sin(3*pi/2) = sin((5*pi/2) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_270_test : -cos(532*pi/3)=1 / 2:=
begin
have : sin(827*pi/6) = cos(532*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (827*pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = -sin(827*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/6) (68),
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


lemma Trigo_271_test : sin(305*pi/2)*cos(143*pi)=cos(pi) / 2 + cos(3*pi) / 2:=
begin
have : - -sin(305 * pi / 2) * cos(143 * pi) = sin(305*pi/2)*cos(143*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(305*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(143 * pi) * cos(pi) = -cos(pi)*cos(143*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -cos(143*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
rw this,
end


lemma Trigo_272_test : -2*sin(pi/2)*cos(369*pi/2)=sin(103*pi):=
begin
have : 2 * sin(pi / 2) * -cos(369 * pi / 2) = -2*sin(pi/2)*cos(369*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(369*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (92),
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
have : sin(pi) = sin(103*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_273_test : -4*sin(637*pi/6)**3 + 3*sin(637*pi/6)=sin(265*pi/2):=
begin
have : 4 * (-sin(637 * pi / 6)) ** 3 - 3 * -sin(637 * pi / 6) = -4*sin(637*pi/6)**3 + 3*sin(637*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(637*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (52),
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
have : cos(2*pi) = sin(265*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_274_test : -sin(pi/2)**2 + cos(-pi) + sin(95*pi)**2=2 * cos(-pi) * cos(0):=
begin
have : cos(pi/2) = sin(95*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) + (-sin(pi / 2) ** 2 + cos(pi / 2) ** 2) = -sin(pi/2)**2 + cos(-pi) + cos(pi/2)**2,
{
field_simp at *,
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
have : cos(-pi) + cos(pi) = 2 * cos(-pi) * cos(0),
{
rw cos_add_cos,
have : cos(((-pi) + (pi))/2) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi) - (pi))/2) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_275_test : sin(13*pi/6)=(sin(0)*sin(pi/6) + cos(0)*cos(pi/6))*sin(2*pi) - sin(-pi/6)*sin(37*pi/2):=
begin
have : cos(2*pi) = sin(37*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2 * pi) * (sin(0) * sin(pi / 6) + cos(0) * cos(pi / 6)) - sin(-pi / 6) * cos(2 * pi) = (sin(0)*sin(pi/6) + cos(0)*cos(pi/6))*sin(2*pi) - sin(-pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(0) * sin(pi/6) + cos(0) * cos(pi/6),
{
have : cos(-pi/6) = cos((0) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(13*pi/6) = sin(2*pi) * cos(-pi/6) - sin(-pi/6) * cos(2*pi),
{
have : sin(13*pi/6) = sin((2*pi) - (-pi/6)),
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


lemma Trigo_276_test : -sin(353*pi/6)*cos(29*pi)=- sin(-13*pi/6) / 2 + sin(-11*pi/6) / 2:=
begin
have : sin(353 * pi / 6) * -cos(29 * pi) = -sin(353*pi/6)*cos(29*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -cos(29*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(353 * pi / 6) * cos((-2) * pi) = sin(353*pi/6)*cos(-2*pi),
{
field_simp at *,
},
have : sin(pi/6) = sin(353*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(-2*pi) = - sin(-13*pi/6) / 2 + sin(-11*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-2*pi) + (pi/6)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi/6)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_277_test : -1 + 2*cos(-pi)**2=- cos(13*pi):=
begin
have : -(1 - cos(-pi) ** 2) + cos(-pi) ** 2 = -1 + 2*cos(-pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) ** 2 = 1 - cos(-pi) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : -sin(-pi) * sin(-pi) + cos(-pi) * cos(-pi) = -sin(-pi)**2 + cos(-pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(-pi) * sin(-pi) + cos(-pi) * cos(-pi),
{
have : cos(-2*pi) = cos((-pi) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = - cos(13*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_278_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) (h2 : (2*(-sin(pi/4)**2+cos(pi/4)**2))≠ 0) : sin(pi)/(2*(-sin(pi/4)**2 + cos(pi/4)**2))=1:=
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


lemma Trigo_279_test : cos(-2*pi/3)=-(sin(-pi/2)*cos(pi/6) + sin(pi/6)*cos(-pi/2))**2 + cos(-2*pi/3)/2 + 1/2:=
begin
have : -(sin(-pi / 2) * cos(pi / 6) + sin(pi / 6) * cos(-pi / 2)) ** 2 + cos((-2) * pi / 3) / 2 + 1 / 2 = -(sin(-pi/2)*cos(pi/6) + sin(pi/6)*cos(-pi/2))**2 + cos(-2*pi/3)/2 + 1/2,
{
field_simp at *,
},
have : sin(-pi/3) = sin(-pi/2) * cos(pi/6) + sin(pi/6) * cos(-pi/2),
{
have : sin(-pi/3) = sin((-pi/2) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : -sin(-pi / 3) ** 2 + (cos((-2) * pi / 3) / 2 + 1 / 2) = -sin(-pi/3)**2 + cos(-2*pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_280_test (h0 : cos(pi/4)≠ 0) (h1 : (sin(5*pi/4)*sin(pi)+cos(5*pi/4)*cos(pi))≠ 0) (h2 : (sin(pi)*sin(5*pi/4)+cos(pi)*cos(5*pi/4))≠ 0) : sin(pi/4)/(sin(pi)*sin(5*pi/4) + cos(pi)*cos(5*pi/4))=1:=
begin
have : sin(pi / 4) / (sin(5 * pi / 4) * sin(pi) + cos(5 * pi / 4) * cos(pi)) = sin(pi/4)/(sin(pi)*sin(5*pi/4) + cos(pi)*cos(5*pi/4)),
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


lemma Trigo_281_test : 1 - 2*sin(15*pi/2)**2=- sin(33*pi/2):=
begin
have : 1 - 2 * (-sin(15 * pi / 2)) ** 2 = 1 - 2*sin(15*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(15*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (3),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi) = - sin(33*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_282_test : cos(pi)=-sin(pi/3)*cos(1057*pi/6) - cos(-371*pi/3)*cos(pi/3):=
begin
have : -sin(pi / 3) * cos(1057 * pi / 6) - cos((-371) * pi / 3) * cos(pi / 3) = -sin(pi/3)*cos(1057*pi/6) - cos(-371*pi/3)*cos(pi/3),
{
field_simp at *,
},
have : sin(1057*pi/6) = cos(-371*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (1057*pi/6) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(sin(1057 * pi / 6) * cos(pi / 3) + sin(pi / 3) * cos(1057 * pi / 6)) = -sin(pi/3)*cos(1057*pi/6) - sin(1057*pi/6)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(353*pi/2) = sin(1057*pi/6) * cos(pi/3) + sin(pi/3) * cos(1057*pi/6),
{
have : sin(353*pi/2) = sin((1057*pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = - sin(353*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_283_test : -cos(955*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(321*pi/4) = -cos(955*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (321*pi/4) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(321*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (40),
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


lemma Trigo_284_test : -cos(278*pi/3)=-sin(527*pi/6)**2 + cos(pi/6)**2:=
begin
have : cos(pi/3) = -cos(278*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(-sin(527 * pi / 6)) ** 2 + cos(pi / 6) ** 2 = -sin(527*pi/6)**2 + cos(pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -sin(527*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (44),
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


lemma Trigo_285_test (h0 : cos(-pi/12)≠ 0) (h1 : (4*cos(-pi/12)**2)≠ 0) (h2 : (2*cos(-pi/12))≠ 0) : -sin(-pi/6)**2/(4*cos(-pi/12)**2) + cos(-pi/12)**2=cos(539*pi/6):=
begin
have : -(sin(-pi / 6) / (2 * cos(-pi / 12))) ** 2 + cos(-pi / 12) ** 2 = -sin(-pi/6)**2/(4*cos(-pi/12)**2) + cos(-pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = sin(-pi/6) / ( 2 * cos(-pi/12) ),
{
have : sin(-pi/6) = sin(2*(-pi/12)),
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
have : cos(-pi/6) = cos(539*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_286_test : -cos(-148*pi/3)=1 / 2:=
begin
have : -cos((-148) * pi / 3) = -cos(-148*pi/3),
{
field_simp at *,
},
have : cos(565*pi/3) = -cos(-148*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (565*pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(565*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (94),
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


lemma Trigo_287_test (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) (h2 : -sin(291*pi/2)≠ 0) (h3 : sin(291*pi/2)≠ 0) : -(3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3)/sin(291*pi/2)=tan(-2*pi):=
begin
have : (3 * sin((-2) * pi / 3) - 4 * sin((-2) * pi / 3) ** 3) / -sin(291 * pi / 2) = -(3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3)/sin(291*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = -sin(291*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin((-2) * pi / 3) ** 3 + 3 * sin((-2) * pi / 3)) / cos((-2) * pi) = (3*sin(-2*pi/3) - 4*sin(-2*pi/3)**3)/cos(-2*pi),
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
have : sin(-2*pi) / cos(-2*pi) = tan(-2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_288_test : -cos(pi/3)*cos(541*pi/3)=-sin(pi/2)/2 - sin(1175*pi/6)/2:=
begin
have : -sin(pi / 2) / 2 + -sin(1175 * pi / 6) / 2 = -sin(pi/2)/2 - sin(1175*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -sin(1175*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -cos(541 * pi / 3) * cos(pi / 3) = -cos(pi/3)*cos(541*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(541*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(pi/3) = - sin(pi/2) / 2 + sin(pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/6)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/6)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_289_test : cos(337*pi/2)=cos(403*pi/2):=
begin
have : cos(pi/2) = cos(337*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos(403 * pi / 2) = cos(403*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(59*pi) = -cos(403*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (59*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(59*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_290_test : cos(-pi/2) - cos(pi/3)=-8*sin(-5*pi/48)*sin(-pi/12)*cos(-5*pi/24)*cos(-5*pi/48):=
begin
have : (-4) * (2 * sin((-5) * pi / 48) * cos((-5) * pi / 48)) * sin(-pi / 12) * cos((-5) * pi / 24) = -8*sin(-5*pi/48)*sin(-pi/12)*cos(-5*pi/24)*cos(-5*pi/48),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/24) = 2 * sin(-5*pi/48) * cos(-5*pi/48),
{
have : sin(-5*pi/24) = sin(2*(-5*pi/48)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : (-2) * (2 * sin((-5) * pi / 24) * cos((-5) * pi / 24)) * sin(-pi / 12) = -4*sin(-5*pi/24)*sin(-pi/12)*cos(-5*pi/24),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/12) = 2 * sin(-5*pi/24) * cos(-5*pi/24),
{
have : sin(-5*pi/12) = sin(2*(-5*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) - cos(pi/3) = - 2 * sin(-5*pi/12) * sin(-pi/12),
{
rw cos_sub_cos,
have : sin(((-pi/2) + (pi/3))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (pi/3))/2) = sin(-5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_291_test : (cos(-5*pi/2)*cos(184*pi) + sin(-5*pi/2)*cos(-pi/2))**2 + cos(-2*pi)**2=1:=
begin
have : (- -cos(184 * pi) * cos((-5) * pi / 2) + sin((-5) * pi / 2) * cos(-pi / 2)) ** 2 + cos((-2) * pi) ** 2 = (cos(-5*pi/2)*cos(184*pi) + sin(-5*pi/2)*cos(-pi/2))**2 + cos(-2*pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(184*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-5) * pi / 2) * cos(-pi / 2) - sin(-pi / 2) * cos((-5) * pi / 2)) ** 2 + cos((-2) * pi) ** 2 = (-sin(-pi/2)*cos(-5*pi/2) + sin(-5*pi/2)*cos(-pi/2))**2 + cos(-2*pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-5*pi/2) * cos(-pi/2) - sin(-pi/2) * cos(-5*pi/2),
{
have : sin(-2*pi) = sin((-5*pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) ** 2 + cos(-2*pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_292_test : cos(593*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -cos(593 * pi / 4) = cos(593*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(215*pi/4) = -cos(593*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (215*pi/4) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(215*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (26),
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


lemma Trigo_293_test : -1 + 2*cos(pi/12)**2=cos(-pi/3)*cos(-pi/6) + sin(-pi/6)*sin(436*pi/3):=
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
have : sin(-pi / 6) * sin(436 * pi / 3) + cos(-pi / 6) * cos(-pi / 3) = cos(-pi/3)*cos(-pi/6) + sin(-pi/6)*sin(436*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = sin(436*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(-pi/6) * sin(-pi/3) + cos(-pi/6) * cos(-pi/3),
{
have : cos(pi/6) = cos((-pi/6) - (-pi/3)),
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


lemma Trigo_294_test (h0 : cos((-2*pi/3)/2)≠ 0) (h1 : sin(-2*pi/3)≠ 0) (h2 : sin((-2)*pi/3)≠ 0) (h3 : cos(1139*pi/6)≠ 0) (h4 : -cos(1139*pi/6)≠ 0) : -(1 - cos(-2*pi/3))/cos(1139*pi/6)=- tan(52*pi/3):=
begin
have : (1 - cos((-2) * pi / 3)) / -cos(1139 * pi / 6) = -(1 - cos(-2*pi/3))/cos(1139*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = -cos(1139*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi/3) (95),
focus{repeat {apply congr_arg _}},
simp,
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
have : tan(-pi/3) = - tan(52*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_295_test : sin(2*pi)*cos(-11*pi/6) - sin(-11*pi/6)*sin(259*pi/2)=- sin(851*pi/6):=
begin
have : sin(2 * pi) * cos((-11) * pi / 6) + sin((-11) * pi / 6) * -sin(259 * pi / 2) = sin(2*pi)*cos(-11*pi/6) - sin(-11*pi/6)*sin(259*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(259*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/6) = - sin(851*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_296_test : sin(1001*pi/6)**2=1 - cos(pi/6) ** 2:=
begin
have : (-sin(1001 * pi / 6)) ** 2 = sin(1001*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(400*pi/3) = -sin(1001*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (400*pi/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(400 * pi / 3)) ** 2 = cos(400*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(400*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (66),
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


lemma Trigo_297_test : -sin(231*pi/2)=-sin(-pi)**2 + cos(2*pi)**2:=
begin
have : -sin(-pi) ** 2 + (-cos(2 * pi)) ** 2 = -sin(-pi)**2 + cos(2*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = -cos(2*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -sin(231*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_298_test (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : (1 - sin(393*pi/2))/sin(2*pi)=0:=
begin
have : cos(2*pi) = sin(393*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (97),
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


lemma Trigo_299_test : sin(pi/6)=sin(-pi/6)*cos(pi/3) + (-1 + 2*cos(37*pi/12)**2)*sin(pi/3):=
begin
have : sin(-pi / 6) * cos(pi / 3) + sin(pi / 3) * (2 * cos(37 * pi / 12) ** 2 - 1) = sin(-pi/6)*cos(pi/3) + (-1 + 2*cos(37*pi/12)**2)*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(37*pi/6) = 2 * cos(37*pi/12) ** 2 - 1,
{
have : cos(37*pi/6) = cos(2*(37*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 3) * cos(37 * pi / 6) + sin(-pi / 6) * cos(pi / 3) = sin(-pi/6)*cos(pi/3) + sin(pi/3)*cos(37*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = cos(37*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = sin(pi/3) * cos(-pi/6) + sin(-pi/6) * cos(pi/3),
{
have : sin(pi/6) = sin((pi/3) + (-pi/6)),
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


lemma Trigo_300_test (h0 : sin(17*pi/4)≠ 0) (h1 : (2*sin(17*pi/4))≠ 0) : sin(17*pi/2)/(2*sin(17*pi/4))=sqrt( 2 ) / 2:=
begin
have : cos(17*pi/4) = sin(17*pi/2) / ( 2 * sin(17*pi/4) ),
{
have : sin(17*pi/2) = sin(2*(17*pi/4)),
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
have : sin(pi/4) = cos(17*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (2),
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


lemma Trigo_301_test : -cos(pi/2)*cos(196*pi/3) - sin(pi/2)*sin(196*pi/3)=sqrt( 3 ) / 2:=
begin
have : -(sin(196 * pi / 3) * sin(pi / 2) + cos(196 * pi / 3) * cos(pi / 2)) = -cos(pi/2)*cos(196*pi/3) - sin(pi/2)*sin(196*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(389*pi/6) = sin(196*pi/3) * sin(pi/2) + cos(196*pi/3) * cos(pi/2),
{
have : cos(389*pi/6) = cos((196*pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(389*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (32),
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


lemma Trigo_302_test : cos(5*pi/3)*cos(35*pi/3) - sin(pi/3)*sin(5*pi/3)=cos(150*pi):=
begin
have : cos(35 * pi / 3) * cos(5 * pi / 3) - sin(pi / 3) * sin(5 * pi / 3) = cos(5*pi/3)*cos(35*pi/3) - sin(pi/3)*sin(5*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(35*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 3) * sin(pi / 3) + cos(5 * pi / 3) * cos(pi / 3) = cos(pi/3)*cos(5*pi/3) - sin(pi/3)*sin(5*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(5*pi/3) * sin(pi/3) + cos(5*pi/3) * cos(pi/3),
{
have : cos(2*pi) = cos((5*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(150*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_303_test : sin(349*pi/6)=sin(341*pi/6):=
begin
have : - -sin(349 * pi / 6) = sin(349*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(46*pi/3) = -sin(349*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (46*pi/3) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(46*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(341*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_304_test : sin(-2*pi)*cos(967*pi/6) + sin(17*pi/6)*cos(-2*pi)=1 / 2:=
begin
have : sin((-2) * pi) * cos(967 * pi / 6) + sin(17 * pi / 6) * cos((-2) * pi) = sin(-2*pi)*cos(967*pi/6) + sin(17*pi/6)*cos(-2*pi),
{
field_simp at *,
},
have : cos(17*pi/6) = cos(967*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (17*pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17 * pi / 6) * cos((-2) * pi) + sin((-2) * pi) * cos(17 * pi / 6) = sin(-2*pi)*cos(17*pi/6) + sin(17*pi/6)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(17*pi/6) * cos(-2*pi) + sin(-2*pi) * cos(17*pi/6),
{
have : sin(5*pi/6) = sin((17*pi/6) + (-2*pi)),
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


lemma Trigo_305_test (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) (h2 : (2*cos(pi/3)**2)≠ 0) (h3 : cos(pi/3)≠ 0) : tan(pi/3)=(sin(pi)*cos(-pi/3) + sin(-pi/3)*cos(pi))/(2*cos(pi/3)**2):=
begin
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
conv {to_rhs, rw ← this,},
have : sin(2 * pi / 3) / (2 * cos(pi / 3)) / cos(pi / 3) = sin(2*pi/3)/(2*cos(pi/3)**2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_306_test (h0 : (-3*cos(pi/6)+4*cos(pi/6)**3)≠ 0) (h1 : (4*cos(pi/6)**3-3*cos(pi/6))≠ 0) : tan(31*pi/2)=sin(pi/2)/(-3*cos(pi/6) + 4*cos(pi/6)**3):=
begin
have : sin(pi / 2) / (4 * cos(pi / 6) ** 3 - 3 * cos(pi / 6)) = sin(pi/2)/(-3*cos(pi/6) + 4*cos(pi/6)**3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(pi/2) = tan(31*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = sin(pi/2) / cos(pi/2),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_307_test (h0 : cos(-pi/6)≠ 0) (h1 : (4*cos(-pi/6)**2)≠ 0) (h2 : (2*cos(-pi/6))≠ 0) : -cos(238*pi/3)=-sin(-pi/3)**2/(4*cos(-pi/6)**2) + cos(-pi/6)**2:=
begin
have : cos(-pi/3) = -cos(238*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(-pi / 3) / (2 * cos(-pi / 6))) ** 2 + cos(-pi / 6) ** 2 = -sin(-pi/3)**2/(4*cos(-pi/6)**2) + cos(-pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
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




lemma Trigo_309_test : cos(-pi/6)*cos(1123*pi/6) - sin(-pi/6)*sin(1123*pi/6)=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : -sin(1123 * pi / 6) * sin(-pi / 6) + cos(1123 * pi / 6) * cos(-pi / 6) = cos(-pi/6)*cos(1123*pi/6) - sin(-pi/6)*sin(1123*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(187*pi) = -sin(1123*pi/6) * sin(-pi/6) + cos(1123*pi/6) * cos(-pi/6),
{
have : cos(187*pi) = cos((1123*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = cos(187*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (3*pi) (95),
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


lemma Trigo_310_test (h0 : cos((457*pi/6)/2)≠ 0) (h1 : (1+cos(457*pi/6))≠ 0) (h2 : (cos(457*pi/6)+1)≠ 0) : sin(457*pi/6)/(cos(457*pi/6) + 1)=2 - sqrt( 3 ):=
begin
have : sin(457 * pi / 6) / (1 + cos(457 * pi / 6)) = sin(457*pi/6)/(cos(457*pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(457*pi/12) = sin(457*pi/6) / ( 1 + cos(457*pi/6) ),
{
have : tan(457*pi/12) = tan((457*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = tan(457*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (38),
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


lemma Trigo_311_test (h0 : cos(-pi/12)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (tan(-pi/3)*tan(-pi/12)+1)≠ 0) (h3 : (1+tan(-pi/12)*tan(-pi/3))≠ 0) (h4 : cos((-pi/6)/2)≠ 0) (h5 : (sin(-pi/6)*tan(-pi/3)/(cos(-pi/6)+1)+1)≠ 0) (h6 : (cos(-pi/6)+1)≠ 0) (h7 : (1+cos(-pi/6))≠ 0) (h8 : (tan(-pi/3)*(sin(-pi/6)/(1+cos(-pi/6)))+1)≠ 0) : (sin(-pi/6)/(cos(-pi/6) + 1) - tan(-pi/3))/(sin(-pi/6)*tan(-pi/3)/(cos(-pi/6) + 1) + 1)=1:=
begin
have : (sin(-pi / 6) / (1 + cos(-pi / 6)) - tan(-pi / 3)) / (tan(-pi / 3) * (sin(-pi / 6) / (1 + cos(-pi / 6))) + 1) = (sin(-pi/6)/(cos(-pi/6) + 1) - tan(-pi/3))/(sin(-pi/6)*tan(-pi/3)/(cos(-pi/6) + 1) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/12) = sin(-pi/6) / ( 1 + cos(-pi/6) ),
{
have : tan(-pi/12) = tan((-pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-pi / 12) - tan(-pi / 3)) / (1 + tan(-pi / 12) * tan(-pi / 3)) = (tan(-pi/12) - tan(-pi/3))/(tan(-pi/3)*tan(-pi/12) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = ( tan(-pi/12) - tan(-pi/3) ) / ( 1 + tan(-pi/12) * tan(-pi/3) ),
{
have : tan(pi/4) = tan((-pi/12) - (-pi/3)),
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


lemma Trigo_312_test : -(1 - 2*sin(-pi/12)**2)*cos(361*pi/2)=- sin(11*pi/6) / 2 + sin(-13*pi/6) / 2:=
begin
have : (1 - 2 * sin(-pi / 12) ** 2) * -cos(361 * pi / 2) = -(1 - 2*sin(-pi/12)**2)*cos(361*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -cos(361*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi) * (1 - 2 * sin(-pi / 12) ** 2) = (1 - 2*sin(-pi/12)**2)*sin(-2*pi),
{
field_simp at *,
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
have : sin(-2*pi) * cos(-pi/6) = - sin(11*pi/6) / 2 + sin(-13*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/6) + (-2*pi)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (-2*pi)) = sin(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_313_test : -sin(79*pi)*cos(-pi) + sin(-pi)*cos(79*pi)=- cos(299*pi/2):=
begin
have : -(sin(79 * pi) * cos(-pi) - sin(-pi) * cos(79 * pi)) = -sin(79*pi)*cos(-pi) + sin(-pi)*cos(79*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(80*pi) = sin(79*pi) * cos(-pi) - sin(-pi) * cos(79*pi),
{
have : sin(80*pi) = sin((79*pi) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(80*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - cos(299*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_314_test : cos(349*pi/2)=3*sin(22*pi) - 4*sin(22*pi)**3:=
begin
have : (-4) * sin(22 * pi) ** 3 + 3 * sin(22 * pi) = 3*sin(22*pi) - 4*sin(22*pi)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(66*pi) = -4 * sin(22*pi) ** 3 + 3 * sin(22*pi),
{
have : sin(66*pi) = sin(3*(22*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(349*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(66*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_315_test : cos(15*pi)=sin(151*pi/2):=
begin
have : - -cos(15 * pi) = cos(15*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(57*pi/2) = -cos(15*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (57*pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -sin(57*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(151*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_316_test (h0 : cos((275*pi/3)/2)≠ 0) (h1 : sin(275*pi/3)≠ 0) : -(1 - cos(275*pi/3))/sin(275*pi/3)=sqrt( 3 ) / 3:=
begin
have : -((1 - cos(275 * pi / 3)) / sin(275 * pi / 3)) = -(1 - cos(275*pi/3))/sin(275*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(275*pi/6) = ( 1 - cos(275*pi/3) ) / sin(275*pi/3),
{
have : tan(275*pi/6) = tan((275*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(275*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (46),
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


lemma Trigo_317_test : sin(pi)*sin(1111*pi/6) + cos(pi)*cos(1111*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(1111 * pi / 6) * sin(pi) + cos(1111 * pi / 6) * cos(pi) = sin(pi)*sin(1111*pi/6) + cos(pi)*cos(1111*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1105*pi/6) = sin(1111*pi/6) * sin(pi) + cos(1111*pi/6) * cos(pi),
{
have : cos(1105*pi/6) = cos((1111*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(1105*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (91),
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


lemma Trigo_318_test (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(-pi/6)*tan(-pi/3))≠ 0) (h3 : (tan(-pi/3)*tan(-pi/6)+1)≠ 0) (h4 : cos(-pi/6)≠ 0) (h5 : (sin(-pi/6)*tan(-pi/3)/cos(-pi/6)+1)≠ 0) (h6 : (tan(-pi/3)*(sin(-pi/6)/cos(-pi/6))+1)≠ 0) : (sin(-pi/6)/cos(-pi/6) - tan(-pi/3))/(sin(-pi/6)*tan(-pi/3)/cos(-pi/6) + 1)=tan(85*pi/6):=
begin
have : (sin(-pi / 6) / cos(-pi / 6) - tan(-pi / 3)) / (tan(-pi / 3) * (sin(-pi / 6) / cos(-pi / 6)) + 1) = (sin(-pi/6)/cos(-pi/6) - tan(-pi/3))/(sin(-pi/6)*tan(-pi/3)/cos(-pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (tan(-pi / 6) - tan(-pi / 3)) / (1 + tan(-pi / 6) * tan(-pi / 3)) = (tan(-pi/6) - tan(-pi/3))/(tan(-pi/3)*tan(-pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(-pi/6) - tan(-pi/3) ) / ( 1 + tan(-pi/6) * tan(-pi/3) ),
{
have : tan(pi/6) = tan((-pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(85*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_319_test : (-4*sin(pi/3)**3 + 3*sin(pi/3))**2 + (cos(-pi)*cos(2*pi) - sin(-pi)*sin(2*pi))**2=1:=
begin
have : ((-4) * sin(pi / 3) ** 3 + 3 * sin(pi / 3)) ** 2 + (-sin(2 * pi) * sin(-pi) + cos(2 * pi) * cos(-pi)) ** 2 = (-4*sin(pi/3)**3 + 3*sin(pi/3))**2 + (cos(-pi)*cos(2*pi) - sin(-pi)*sin(2*pi))**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(2*pi) * sin(-pi) + cos(2*pi) * cos(-pi),
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
conv {to_lhs, rw ← this,},
have : ((-4) * sin(pi / 3) ** 3 + 3 * sin(pi / 3)) ** 2 + cos(pi) ** 2 = (-4*sin(pi/3)**3 + 3*sin(pi/3))**2 + cos(pi)**2,
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
have : sin(pi) ** 2 + cos(pi) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_320_test : cos(15*pi/2)=cos(279*pi/2):=
begin
have : sin(85*pi) = cos(15*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (85*pi) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = sin(85*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(279*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_321_test (h0 : cos(pi/3)≠ 0) (h1 : (2*sin(329*pi/6))≠ 0) : -sin(40*pi/3)=sin(2*pi/3)/(2*sin(329*pi/6)):=
begin
have : sin(pi/3) = -sin(40*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(329*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_322_test (h0 : cos(199*pi/6)≠ 0) : sin(199*pi/6)/cos(199*pi/6)=sqrt( 3 ) / 3:=
begin
have : tan(199*pi/6) = sin(199*pi/6) / cos(199*pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = tan(199*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (pi/6) (33),
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


lemma Trigo_323_test : cos(-pi/3)=sin(518*pi/3)*cos(-pi/2) - cos(98*pi)*cos(518*pi/3):=
begin
have : sin(518 * pi / 3) * cos(-pi / 2) + -cos(98 * pi) * cos(518 * pi / 3) = sin(518*pi/3)*cos(-pi/2) - cos(98*pi)*cos(518*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -cos(98*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(1033*pi/6) = sin(518*pi/3) * cos(-pi/2) + sin(-pi/2) * cos(518*pi/3),
{
have : sin(1033*pi/6) = sin((518*pi/3) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = sin(1033*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_324_test : 2*sin(92*pi)*cos(92*pi)=0:=
begin
have : sin(184*pi) = 2 * sin(92*pi) * cos(92*pi),
{
have : sin(184*pi) = sin(2*(92*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(184*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (92),
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


lemma Trigo_325_test : -(-4*sin(5*pi/36)**3 + 3*sin(5*pi/36))**2 + cos(5*pi/12)**2=sin(pi/2) * sin(-pi/3) + cos(pi/2) * cos(-pi/3):=
begin
have : -((-4) * sin(5 * pi / 36) ** 3 + 3 * sin(5 * pi / 36)) ** 2 + cos(5 * pi / 12) ** 2 = -(-4*sin(5*pi/36)**3 + 3*sin(5*pi/36))**2 + cos(5*pi/12)**2,
{
field_simp at *,
},
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


lemma Trigo_326_test : -sin(310*pi)=0:=
begin
have : sin(147*pi) = -sin(310*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (147*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(147*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (73),
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


lemma Trigo_327_test : -cos(-pi)*cos(pi) - sin(-pi)*sin(pi) + cos(pi/3)=2*sin(7*pi/6)*sin(785*pi/6):=
begin
have : cos(pi / 3) - (sin(pi) * sin(-pi) + cos(pi) * cos(-pi)) = -cos(-pi)*cos(pi) - sin(-pi)*sin(pi) + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(pi) * sin(-pi) + cos(pi) * cos(-pi),
{
have : cos(2*pi) = cos((pi) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * -sin(785 * pi / 6) * sin(7 * pi / 6) = 2*sin(7*pi/6)*sin(785*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/6) = -sin(785*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) - cos(2*pi) = - 2 * sin(-5*pi/6) * sin(7*pi/6),
{
rw cos_sub_cos,
have : sin(((pi/3) + (2*pi))/2) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (2*pi))/2) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_328_test : sin(-pi) + sin(139*pi)=2 * sin(-pi) * cos(0):=
begin
have : sin(39*pi) = sin(139*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (39*pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) - -sin(39 * pi) = sin(-pi) + sin(39*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(39*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) - sin(pi) = 2 * sin(-pi) * cos(0),
{
rw sin_sub_sin,
have : cos(((-pi) + (pi))/2) = cos(0),
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
},
rw this,
end


lemma Trigo_329_test (h0 : cos(589*pi/3)≠ 0) (h1 : (2*cos(589*pi/3))≠ 0) : sin(1178*pi/3)*cos(pi/3)/(2*cos(589*pi/3))=cos(-pi/2) / 2 + cos(pi/6) / 2:=
begin
have : sin(1178 * pi / 3) / (2 * cos(589 * pi / 3)) * cos(pi / 3) = sin(1178*pi/3)*cos(pi/3)/(2*cos(589*pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(589*pi/3) = sin(1178*pi/3) / ( 2 * cos(589*pi/3) ),
{
have : sin(1178*pi/3) = sin(2*(589*pi/3)),
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
have : cos(-pi/6) = sin(589*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) * cos(pi/3) = cos(-pi/2) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (pi/3)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (pi/3)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_330_test : cos(-pi)=sin(-289*pi/2):=
begin
have : - -sin((-289) * pi / 2) = sin(-289*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(493*pi/2) = -sin(-289*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (493*pi/2) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(215*pi/2) = -sin(493*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (215*pi/2) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(215*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_331_test : 1 - 2*sin(pi/4)**2=sin(313*pi):=
begin
have : - -sin(313 * pi) = sin(313*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(335*pi/2) = -sin(313*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (335*pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
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
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(335*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_332_test : sin(-11*pi/6)*sin(70*pi) + cos(-11*pi/6)*cos(2*pi)=sqrt( 3 ) / 2:=
begin
have : -sin((-11) * pi / 6) * -sin(70 * pi) + cos((-11) * pi / 6) * cos(2 * pi) = sin(-11*pi/6)*sin(70*pi) + cos(-11*pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(70*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_333_test (h0 : cos((260*pi/3)/2)≠ 0) (h1 : sin(260*pi/3)≠ 0) : -(1 - cos(260*pi/3))/sin(260*pi/3)=- sqrt( 3 ):=
begin
have : -((1 - cos(260 * pi / 3)) / sin(260 * pi / 3)) = -(1 - cos(260*pi/3))/sin(260*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(130*pi/3) = ( 1 - cos(260*pi/3) ) / sin(260*pi/3),
{
have : tan(130*pi/3) = tan((260*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(130*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (44),
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


lemma Trigo_334_test : cos(225*pi/2)/2 + cos(671*pi/6)/2=cos(-pi/6) / 2 + cos(pi/2) / 2:=
begin
have : cos(671 * pi / 6) / 2 + cos(225 * pi / 2) / 2 = cos(225*pi/2)/2 + cos(671*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(673*pi/6) * cos(pi/3) = cos(671*pi/6) / 2 + cos(225*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((673*pi/6) + (pi/3)) = cos(225*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((673*pi/6) - (pi/3)) = cos(671*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(673*pi/6) * cos(pi/3)) = cos(pi/3)*cos(673*pi/6),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(673 * pi / 6) * cos(pi / 3) = cos(pi/3)*cos(673*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(673*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (56),
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


lemma Trigo_335_test : sin(-2*pi)=-sin(-pi/3)*sin(1111*pi/6) + sin(1154*pi/3)*cos(-pi/3):=
begin
have : -sin(-pi / 3) * sin(1111 * pi / 6) - cos(-pi / 3) * -sin(1154 * pi / 3) = -sin(-pi/3)*sin(1111*pi/6) + sin(1154*pi/3)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(1111*pi/6) = -sin(1154*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (1111*pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(sin(1111 * pi / 6) * sin(-pi / 3) + cos(1111 * pi / 6) * cos(-pi / 3)) = -sin(-pi/3)*sin(1111*pi/6) - cos(-pi/3)*cos(1111*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(371*pi/2) = sin(1111*pi/6) * sin(-pi/3) + cos(1111*pi/6) * cos(-pi/3),
{
have : cos(371*pi/2) = cos((1111*pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = - cos(371*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_336_test : sin(213*pi/2)=1 - 2*(sin(5*pi/2)*cos(pi/2) - sin(pi/2)*cos(5*pi/2))**2:=
begin
have : cos(4*pi) = sin(213*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (4*pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(5*pi/2) * cos(pi/2) - sin(pi/2) * cos(5*pi/2),
{
have : sin(2*pi) = sin((5*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
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


lemma Trigo_337_test : -1 + 2*(-sin(-7*pi/12)*sin(pi) + cos(-7*pi/12)*cos(pi))**2=- sqrt( 3 ) / 2:=
begin
have : -1 + 2 * (-sin((-7) * pi / 12) * sin(pi) + cos((-7) * pi / 12) * cos(pi)) ** 2 = -1 + 2*(-sin(-7*pi/12)*sin(pi) + cos(-7*pi/12)*cos(pi))**2,
{
field_simp at *,
},
have : cos(5*pi/12) = -sin(-7*pi/12) * sin(pi) + cos(-7*pi/12) * cos(pi),
{
have : cos(5*pi/12) = cos((-7*pi/12) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(5 * pi / 12) ** 2 - 1 = -1 + 2*cos(5*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = 2 * cos(5*pi/12) ** 2 - 1,
{
have : cos(5*pi/6) = cos(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end




lemma Trigo_339_test : sin(-pi)*cos(4*pi/3) + sin(4*pi/3)*cos(-pi)=2*sin(pi/6)*cos(745*pi/6):=
begin
have : sin(4 * pi / 3) * cos(-pi) + sin(-pi) * cos(4 * pi / 3) = sin(-pi)*cos(4*pi/3) + sin(4*pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(4*pi/3) * cos(-pi) + sin(-pi) * cos(4*pi/3),
{
have : sin(pi/3) = sin((4*pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(745*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_340_test : -sin(29*pi/6)*cos(-2*pi) - sin(-2*pi)*sin(8*pi/3)=- 1 / 2:=
begin
have : cos((-2) * pi) * -sin(29 * pi / 6) - sin((-2) * pi) * sin(8 * pi / 3) = -sin(29*pi/6)*cos(-2*pi) - sin(-2*pi)*sin(8*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi/3) = -sin(29*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/3) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(8 * pi / 3) * sin((-2) * pi) + cos(8 * pi / 3) * cos((-2) * pi) = cos(-2*pi)*cos(8*pi/3) - sin(-2*pi)*sin(8*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(8*pi/3) * sin(-2*pi) + cos(8*pi/3) * cos(-2*pi),
{
have : cos(2*pi/3) = cos((8*pi/3) + (-2*pi)),
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


lemma Trigo_341_test : sin(-9*pi/2)=- 1:=
begin
have : - -sin((-9) * pi / 2) = sin(-9*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(94*pi) = -sin(-9*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (94*pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(94*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (47),
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


lemma Trigo_342_test : (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(-13*pi/6) - sin(-2*pi)*cos(-13*pi/6)=sin(-pi/2) * cos(pi/3) + sin(pi/3) * cos(-pi/2):=
begin
have : sin((-13) * pi / 6) * (4 * cos((-2) * pi / 3) ** 3 - 3 * cos((-2) * pi / 3)) - sin((-2) * pi) * cos((-13) * pi / 6) = (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*sin(-13*pi/6) - sin(-2*pi)*cos(-13*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin((-13) * pi / 6) * cos((-2) * pi) - sin((-2) * pi) * cos((-13) * pi / 6) = sin(-13*pi/6)*cos(-2*pi) - sin(-2*pi)*cos(-13*pi/6),
{
field_simp at *,
},
have : sin(-pi/6) = sin(-13*pi/6) * cos(-2*pi) - sin(-2*pi) * cos(-13*pi/6),
{
have : sin(-pi/6) = sin((-13*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(-pi/2) * cos(pi/3) + sin(pi/3) * cos(-pi/2),
{
have : sin(-pi/6) = sin((-pi/2) + (pi/3)),
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


lemma Trigo_343_test : cos(0)=-sin(-pi/6)*sin(pi/6) + sin(146*pi/3)*sin(206*pi/3):=
begin
have : cos(-pi/6) = sin(206*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -sin(pi / 6) * sin(-pi / 6) + sin(146 * pi / 3) * cos(-pi / 6) = -sin(-pi/6)*sin(pi/6) + sin(146*pi/3)*cos(-pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(146*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(0) = - sin(pi/6) * sin(-pi/6) + cos(pi/6) * cos(-pi/6),
{
have : cos(0) = cos((pi/6) + (-pi/6)),
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


lemma Trigo_344_test : -2*sin(pi/4)*sin(415*pi/4)=1:=
begin
have : 2 * sin(pi / 4) * -sin(415 * pi / 4) = -2*sin(pi/4)*sin(415*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(415*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (51),
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


lemma Trigo_345_test : 1 - 2*sin(121*pi/6)**2=1 / 2:=
begin
have : cos(121*pi/3) = 1 - 2 * sin(121*pi/6) ** 2,
{
have : cos(121*pi/3) = cos(2*(121*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(121*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (20),
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


lemma Trigo_346_test (h0 : tan(131*pi/4)≠ 0) (h1 : ((-1)/tan(469*pi/4))≠ 0) (h2 : tan(469*pi/4)≠ 0) : tan(469*pi/4)=1:=
begin
have : (-1) / ((-1) / tan(469 * pi / 4)) = tan(469*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(131*pi/4) = -1 / tan(469*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (131*pi/4) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(131 * pi / 4) = -1/tan(131*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(131*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (32),
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


lemma Trigo_347_test : -sin(-23*pi/12)*sin(2*pi) + sin(29*pi/2)*cos(-23*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -sin((-23) * pi / 12) * sin(2 * pi) + cos((-23) * pi / 12) * sin(29 * pi / 2) = -sin(-23*pi/12)*sin(2*pi) + sin(29*pi/2)*cos(-23*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(29*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-23) * pi / 12) * sin(2 * pi) + cos((-23) * pi / 12) * cos(2 * pi) = -sin(-23*pi/12)*sin(2*pi) + cos(-23*pi/12)*cos(2*pi),
{
field_simp at *,
},
have : cos(pi/12) = -sin(-23*pi/12) * sin(2*pi) + cos(-23*pi/12) * cos(2*pi),
{
have : cos(pi/12) = cos((-23*pi/12) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw cos_pi_div_twelve,
},
rw this,
end


lemma Trigo_348_test : sin(5*pi/6)=sin(pi/3)*sin(156*pi) + (cos(pi/6)*cos(pi/2) + sin(pi/6)*sin(pi/2))*sin(pi/2):=
begin
have : sin(pi / 3) * sin(156 * pi) + sin(pi / 2) * (sin(pi / 2) * sin(pi / 6) + cos(pi / 2) * cos(pi / 6)) = sin(pi/3)*sin(156*pi) + (cos(pi/6)*cos(pi/2) + sin(pi/6)*sin(pi/2))*sin(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi / 2) * cos(pi / 3) + sin(pi / 3) * sin(156 * pi) = sin(pi/3)*sin(156*pi) + sin(pi/2)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(156*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/6) = sin(pi/2) * cos(pi/3) + sin(pi/3) * cos(pi/2),
{
have : sin(5*pi/6) = sin((pi/2) + (pi/3)),
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


lemma Trigo_349_test : -sin(433*pi/6)=2 * cos(pi/3) ** 2 - 1:=
begin
have : cos(205*pi/3) = sin(433*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (205*pi/3) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -cos(205*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (34),
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




lemma Trigo_351_test : sin(128*pi)=-1 + 2*sin(195*pi/4)**2:=
begin
have : sin(-pi) = sin(128*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - 2 * sin(195 * pi / 4) ** 2) = -1 + 2*sin(195*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(195*pi/2) = 1 - 2 * sin(195*pi/4) ** 2,
{
have : cos(195*pi/2) = cos(2*(195*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = - cos(195*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_352_test : sin(3847*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -sin(3847 * pi / 12) = sin(3847*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1675*pi/12) = -sin(3847*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (1675*pi/12) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(1675*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (69),
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


lemma Trigo_353_test (h0 : sin(275*pi/2)≠ 0) (h1 : (2*sin(275*pi/2))≠ 0) : sin(275*pi)/(2*sin(275*pi/2))=0:=
begin
have : cos(275*pi/2) = sin(275*pi) / ( 2 * sin(275*pi/2) ),
{
have : sin(275*pi) = sin(2*(275*pi/2)),
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
have : cos(pi/2) = cos(275*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (69),
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


lemma Trigo_354_test : -cos(-4*pi/3)*cos(-pi) - sin(-4*pi/3)*sin(-pi) - sin(259*pi/2)=- 2 * sin(7*pi/6) * sin(5*pi/6):=
begin
have : -(sin((-4) * pi / 3) * sin(-pi) + cos((-4) * pi / 3) * cos(-pi)) - sin(259 * pi / 2) = -cos(-4*pi/3)*cos(-pi) - sin(-4*pi/3)*sin(-pi) - sin(259*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(-4*pi/3) * sin(-pi) + cos(-4*pi/3) * cos(-pi),
{
have : cos(-pi/3) = cos((-4*pi/3) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(259 * pi / 2) - cos(-pi / 3) = -cos(-pi/3) - sin(259*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(259*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_355_test (h0 : cos((2*pi/3)/2)≠ 0) (h1 : sin(2*pi/3)≠ 0) (h2 : (2*sin(pi/3)*cos(pi/3))≠ 0) : (1 - cos(2*pi/3))/(2*sin(pi/3)*cos(pi/3))=sqrt( 3 ):=
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


lemma Trigo_356_test (h0 : cos(pi/2)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan(pi/2)*tan(-pi/2))≠ 0) (h3 : (tan(-pi/2)*tan(pi/2)+1)≠ 0) (h4 : cos(-3*pi/2)≠ 0) (h5 : cos(-pi)≠ 0) (h6 : (1+tan((-3)*pi/2)*tan(-pi))≠ 0) (h7 : (1+(-tan(-pi)+tan(-3*pi/2))*tan(pi/2)/(tan(-3*pi/2)*tan(-pi)+1))≠ 0) (h8 : (tan(-3*pi/2)*tan(-pi)+1)≠ 0) (h9 : ((tan((-3)*pi/2)-tan(-pi))/(1+tan((-3)*pi/2)*tan(-pi))*tan(pi/2)+1)≠ 0) : (-(-tan(-pi) + tan(-3*pi/2))/(tan(-3*pi/2)*tan(-pi) + 1) + tan(pi/2))/(1 + (-tan(-pi) + tan(-3*pi/2))*tan(pi/2)/(tan(-3*pi/2)*tan(-pi) + 1))=0:=
begin
have : (-((tan((-3) * pi / 2) - tan(-pi)) / (1 + tan((-3) * pi / 2) * tan(-pi))) + tan(pi / 2)) / ((tan((-3) * pi / 2) - tan(-pi)) / (1 + tan((-3) * pi / 2) * tan(-pi)) * tan(pi / 2) + 1) = (-(-tan(-pi) + tan(-3*pi/2))/(tan(-3*pi/2)*tan(-pi) + 1) + tan(pi/2))/(1 + (-tan(-pi) + tan(-3*pi/2))*tan(pi/2)/(tan(-3*pi/2)*tan(-pi) + 1)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = ( tan(-3*pi/2) - tan(-pi) ) / ( 1 + tan(-3*pi/2) * tan(-pi) ),
{
have : tan(-pi/2) = tan((-3*pi/2) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 2) - tan(-pi / 2)) / (1 + tan(pi / 2) * tan(-pi / 2)) = (-tan(-pi/2) + tan(pi/2))/(tan(-pi/2)*tan(pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(pi/2) - tan(-pi/2) ) / ( 1 + tan(pi/2) * tan(-pi/2) ),
{
have : tan(pi) = tan((pi/2) - (-pi/2)),
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


lemma Trigo_357_test : -1 + 2*sin(117*pi/2)**2=- sin(399*pi/2):=
begin
have : -1 + 2 * (-sin(117 * pi / 2)) ** 2 = -1 + 2*sin(117*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(117*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(2*pi) = - sin(399*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_358_test : -sin(-pi)*sin(157*pi/4) + sin(7*pi/4)*cos(-pi)=sqrt( 2 ) / 2:=
begin
have : sin(-pi) * -sin(157 * pi / 4) + sin(7 * pi / 4) * cos(-pi) = -sin(-pi)*sin(157*pi/4) + sin(7*pi/4)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/4) = -sin(157*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/4) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 4) * cos(-pi) + sin(-pi) * cos(7 * pi / 4) = sin(-pi)*cos(7*pi/4) + sin(7*pi/4)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(7*pi/4) * cos(-pi) + sin(-pi) * cos(7*pi/4),
{
have : sin(3*pi/4) = sin((7*pi/4) + (-pi)),
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


lemma Trigo_359_test : -sin(217*pi/2)=-3*cos(239*pi/3) + 4*cos(239*pi/3)**3:=
begin
have : 4 * cos(239 * pi / 3) ** 3 - 3 * cos(239 * pi / 3) = -3*cos(239*pi/3) + 4*cos(239*pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = cos(239*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -sin(217*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (54),
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


lemma Trigo_360_test : 3*sin(-13*pi/6)*cos(-2*pi) - 3*sin(-2*pi)*cos(-13*pi/6) - 4*(sin(-13*pi/6)*cos(-2*pi) - sin(-2*pi)*cos(-13*pi/6))**3=- sin(37*pi/2):=
begin
have : 3 * (sin((-13) * pi / 6) * cos((-2) * pi) - sin((-2) * pi) * cos((-13) * pi / 6)) - 4 * (sin((-13) * pi / 6) * cos((-2) * pi) - sin((-2) * pi) * cos((-13) * pi / 6)) ** 3 = 3*sin(-13*pi/6)*cos(-2*pi) - 3*sin(-2*pi)*cos(-13*pi/6) - 4*(sin(-13*pi/6)*cos(-2*pi) - sin(-2*pi)*cos(-13*pi/6))**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(-13*pi/6) * cos(-2*pi) - sin(-2*pi) * cos(-13*pi/6),
{
have : sin(-pi/6) = sin((-13*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(-pi/2) = - sin(37*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_361_test : (sin(pi)*sin(260*pi/3) + cos(pi)*cos(260*pi/3))**2=1 / 2 - cos(pi/3) / 2:=
begin
have : (sin(260 * pi / 3) * sin(pi) + cos(260 * pi / 3) * cos(pi)) ** 2 = (sin(pi)*sin(260*pi/3) + cos(pi)*cos(260*pi/3))**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(257*pi/3) = sin(260*pi/3) * sin(pi) + cos(260*pi/3) * cos(pi),
{
have : cos(257*pi/3) = cos((260*pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(257*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (42),
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


lemma Trigo_362_test : -cos(46*pi/3)=-sin(1843*pi/6):=
begin
have : sin(925*pi/6) = -sin(1843*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (925*pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -cos(46*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(925*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_363_test (h0 : (-sin(pi/6)**2+cos(pi/6)**2)≠ 0) (h1 : cos((2*pi/3)/2)≠ 0) (h2 : sin(2*pi/3)≠ 0) : sin(pi/3)/(-sin(pi/6)**2 + cos(pi/6)**2)=(1 - cos(2*pi/3))/sin(2*pi/3):=
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
conv {to_rhs, rw ← this,},
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
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_364_test : cos(pi/2)=sin(91*pi):=
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
have : cos(pi/2) = sin(91*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_365_test : -cos(140*pi)=cos(101*pi):=
begin
have : cos(110*pi) = cos(140*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (110*pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(110*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(101*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_367_test : -sin(767*pi/12)**2 + cos(767*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : cos(767*pi/6) = -sin(767*pi/12) ** 2 + cos(767*pi/12) ** 2,
{
have : cos(767*pi/6) = cos(2*(767*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(767*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (64),
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




lemma Trigo_369_test : cos(529*pi/2)=sin(71*pi):=
begin
have : - -cos(529 * pi / 2) = cos(529*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(192*pi) = -cos(529*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (192*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(192*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = sin(71*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_370_test : 1 - 2*sin(pi/4)**2=4*sin(48*pi)**3 - 3*sin(48*pi):=
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
have : -((-4) * sin(48 * pi) ** 3 + 3 * sin(48 * pi)) = 4*sin(48*pi)**3 - 3*sin(48*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(144*pi) = -4 * sin(48*pi) ** 3 + 3 * sin(48*pi),
{
have : sin(144*pi) = sin(3*(48*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = - sin(144*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_371_test : -sin(-pi/12)**2 + cos(-pi/12)**2=cos(1895*pi/6):=
begin
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
have : - -cos(1895 * pi / 6) = cos(1895*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(502*pi/3) = -cos(1895*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (502*pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(502*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_372_test (h0 : cos(25*pi/12)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (1+tan(25*pi/12)*tan(2*pi))≠ 0) (h3 : (tan(2*pi)*tan(25*pi/12)+1)≠ 0) (h4 : cos(25*pi/12)≠ 0) (h5 : cos(2*pi)≠ 0) (h6 : tan((25*pi/12)+(2*pi))≠ 0) (h7 : 1-tan(25*pi/12)*tan(2*pi)≠ 0) (h8 : (-(tan(25*pi/12)+tan(2*pi))/tan(49*pi/12)+1+1)≠ 0) (h9 : tan(49*pi/12)≠ 0) (h10 : ((-tan(25*pi/12)-tan(2*pi))/tan(49*pi/12)+2)≠ 0) : (-tan(2*pi) + tan(25*pi/12))/((-tan(25*pi/12) - tan(2*pi))/tan(49*pi/12) + 2)=2 - sqrt( 3 ):=
begin
have : (-tan(2 * pi) + tan(25 * pi / 12)) / (-(tan(25 * pi / 12) + tan(2 * pi)) / tan(49 * pi / 12) + 1 + 1) = (-tan(2*pi) + tan(25*pi/12))/((-tan(25*pi/12) - tan(2*pi))/tan(49*pi/12) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(25*pi/12) * tan(2*pi) = -( tan(25*pi/12) + tan(2*pi) ) / tan(49*pi/12) + 1,
{
rw tan_mul_tan',
have : tan((25*pi/12) + (2*pi)) = tan(49*pi/12),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(25*pi/12) * tan(2*pi)) = tan(2*pi)*tan(25*pi/12),
{
ring,
},
conv {to_lhs, rw this,},
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


lemma Trigo_373_test : cos(769*pi/6)=4*sin(pi/6)*cos(pi/6)*cos(pi/3):=
begin
have : 2 * (2 * sin(pi / 6) * cos(pi / 6)) * cos(pi / 3) = 4*sin(pi/6)*cos(pi/6)*cos(pi/3),
{
field_simp at *,
ring,
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
conv {to_rhs, rw ← this,},
have : sin(2*pi/3) = cos(769*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_374_test : -sin(pi/6)*cos(91*pi/3)=sin(-pi/6)*sin(pi/6):=
begin
have : sin(pi / 6) * -cos(91 * pi / 3) = -sin(pi/6)*cos(91*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(91*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / 2 * ((-2) * sin(-pi / 6) * sin(pi / 6)) = sin(-pi/6)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(0) - cos(pi/3) = -2 * sin(-pi/6) * sin(pi/6),
{
rw cos_sub_cos,
have : sin(((0) + (pi/3))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((0) - (pi/3))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : -1/2*(cos(0) - cos(pi/3)) = cos(pi/3)/2-cos(0)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/6) * sin(-pi/6) = cos(pi/3) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_375_test : -cos(63*pi)=1:=
begin
have : sin(79*pi/2) = cos(63*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (79*pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(79*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (19),
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


lemma Trigo_376_test (h0 : cos(226*pi/3)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (tan(2*pi)*tan(226*pi/3)+1)≠ 0) (h3 : (1+tan(226*pi/3)*tan(2*pi))≠ 0) : (-tan(2*pi) + tan(226*pi/3))/(tan(2*pi)*tan(226*pi/3) + 1)=sqrt( 3 ):=
begin
have : (tan(226 * pi / 3) - tan(2 * pi)) / (1 + tan(226 * pi / 3) * tan(2 * pi)) = (-tan(2*pi) + tan(226*pi/3))/(tan(2*pi)*tan(226*pi/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(220*pi/3) = ( tan(226*pi/3) - tan(2*pi) ) / ( 1 + tan(226*pi/3) * tan(2*pi) ),
{
have : tan(220*pi/3) = tan((226*pi/3) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(220*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (73),
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


lemma Trigo_377_test : -2*sin(-pi/6)**2 + 1 + sin(369*pi/2)=2 * cos(5*pi/6) * cos(-7*pi/6):=
begin
have : 1 - 2 * sin(-pi / 6) ** 2 + sin(369 * pi / 2) = -2*sin(-pi/6)**2 + 1 + sin(369*pi/2),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(369*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(-2*pi) = 2 * cos(5*pi/6) * cos(-7*pi/6),
{
rw cos_add_cos,
have : cos(((-pi/3) + (-2*pi))/2) = cos(-7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/3) - (-2*pi))/2) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_378_test : -3*sin(433*pi/18) + 4*sin(433*pi/18)**3=sin(547*pi/6):=
begin
have : -((-4) * sin(433 * pi / 18) ** 3 + 3 * sin(433 * pi / 18)) = -3*sin(433*pi/18) + 4*sin(433*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(433*pi/6) = -4 * sin(433*pi/18) ** 3 + 3 * sin(433*pi/18),
{
have : sin(433*pi/6) = sin(3*(433*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(433*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(547*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_379_test : sin(-pi/6) - sin(-pi/3)=(-2*sin(-pi)*sin(3*pi/4) + 2*cos(3*pi/4)*cos(163*pi))*sin(pi/12):=
begin
have : 2 * (-sin(-pi) * sin(3 * pi / 4) + cos(163 * pi) * cos(3 * pi / 4)) * sin(pi / 12) = (-2*sin(-pi)*sin(3*pi/4) + 2*cos(3*pi/4)*cos(163*pi))*sin(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = cos(163*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin(pi / 12) * (-sin(3 * pi / 4) * sin(-pi) + cos(3 * pi / 4) * cos(-pi)) = 2*(-sin(-pi)*sin(3*pi/4) + cos(-pi)*cos(3*pi/4))*sin(pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = -sin(3*pi/4) * sin(-pi) + cos(3*pi/4) * cos(-pi),
{
have : cos(-pi/4) = cos((3*pi/4) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_380_test (h0 : cos((pi/2)/2)≠ 0) (h1 : sin(pi/2)≠ 0) : (1 - cos(41*pi/2))/sin(pi/2)=1:=
begin
have : cos(pi/2) = cos(41*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (10),
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


lemma Trigo_381_test : (-1 + 2*cos(197*pi/2)**2)*sin(-pi/3)=sin(-4*pi/3) / 2 + sin(2*pi/3) / 2:=
begin
have : sin(-pi / 3) * (2 * cos(197 * pi / 2) ** 2 - 1) = (-1 + 2*cos(197*pi/2)**2)*sin(-pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(197*pi) = 2 * cos(197*pi/2) ** 2 - 1,
{
have : cos(197*pi) = cos(2*(197*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(197*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi) = sin(-4*pi/3) / 2 + sin(2*pi/3) / 2,
{
rw sin_mul_cos,
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
},
rw this,
end


lemma Trigo_382_test : 1 - 2*sin(pi/4)**2=cos(149*pi/2):=
begin
have : -1 + 2 * (1 - sin(pi / 4) ** 2) = 1 - 2*sin(pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) ** 2 = 1 - sin(pi/4) ** 2,
{
rw cos_sq',
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
have : cos(pi/2) = cos(149*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_383_test : -sin(-2*pi)*cos(-3*pi/2) + sin(-3*pi/2)*cos(76*pi)=1:=
begin
have : -sin((-2) * pi) * cos((-3) * pi / 2) + sin((-3) * pi / 2) * cos(76 * pi) = -sin(-2*pi)*cos(-3*pi/2) + sin(-3*pi/2)*cos(76*pi),
{
field_simp at *,
},
have : cos(-2*pi) = cos(76*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-3) * pi / 2) * cos((-2) * pi) - sin((-2) * pi) * cos((-3) * pi / 2) = -sin(-2*pi)*cos(-3*pi/2) + sin(-3*pi/2)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_384_test : sin(1141*pi/6)=sin(-pi/3)*sin(2*pi) + (-sin(-pi/6)**2 + cos(-pi/6)**2)*cos(2*pi):=
begin
have : sin(2 * pi) * sin(-pi / 3) + cos(2 * pi) * (-sin(-pi / 6) ** 2 + cos(-pi / 6) ** 2) = sin(-pi/3)*sin(2*pi) + (-sin(-pi/6)**2 + cos(-pi/6)**2)*cos(2*pi),
{
field_simp at *,
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
have : cos(7*pi/3) = sin(1141*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/3) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/3) = sin(2*pi) * sin(-pi/3) + cos(2*pi) * cos(-pi/3),
{
have : cos(7*pi/3) = cos((2*pi) - (-pi/3)),
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


lemma Trigo_385_test : -cos(pi/3)/2 + 1/2 + (cos(-pi/2)*cos(2*pi/3) - sin(-pi/2)*sin(2*pi/3))**2=1:=
begin
have : 1 / 2 - cos(pi / 3) / 2 + (cos(-pi / 2) * cos(2 * pi / 3) - sin(-pi / 2) * sin(2 * pi / 3)) ** 2 = -cos(pi/3)/2 + 1/2 + (cos(-pi/2)*cos(2*pi/3) - sin(-pi/2)*sin(2*pi/3))**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi / 6) ** 2 + (-sin(2 * pi / 3) * sin(-pi / 2) + cos(2 * pi / 3) * cos(-pi / 2)) ** 2 = sin(pi/6)**2 + (cos(-pi/2)*cos(2*pi/3) - sin(-pi/2)*sin(2*pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(2*pi/3) * sin(-pi/2) + cos(2*pi/3) * cos(-pi/2),
{
have : cos(pi/6) = cos((2*pi/3) + (-pi/2)),
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


lemma Trigo_386_test : 16*sin(pi/2)**2*cos(pi/2)**2*cos(pi)**2=1 / 2 - cos(4*pi) / 2:=
begin
have : 4 * (2 * sin(pi / 2) * cos(pi / 2)) ** 2 * cos(pi) ** 2 = 16*sin(pi/2)**2*cos(pi/2)**2*cos(pi)**2,
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
have : (2 * sin(pi) * cos(pi)) ** 2 = 4*sin(pi)**2*cos(pi)**2,
{
field_simp at *,
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


lemma Trigo_387_test : cos(554*pi/3)**2 + cos(1181*pi/6)**2=1:=
begin
have : cos(554 * pi / 3) ** 2 + (-cos(1181 * pi / 6)) ** 2 = cos(554*pi/3)**2 + cos(1181*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(1181*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) ** 2 + (-cos(554 * pi / 3)) ** 2 = cos(554*pi/3)**2 + sin(pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(554*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (92),
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


lemma Trigo_388_test : cos(-pi/2)*cos(677*pi/6) - sin(-pi/2)*sin(677*pi/6)=- cos(238*pi/3):=
begin
have : -sin(677 * pi / 6) * sin(-pi / 2) + cos(677 * pi / 6) * cos(-pi / 2) = cos(-pi/2)*cos(677*pi/6) - sin(-pi/2)*sin(677*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(337*pi/3) = -sin(677*pi/6) * sin(-pi/2) + cos(677*pi/6) * cos(-pi/2),
{
have : cos(337*pi/3) = cos((677*pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(337*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(238*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_389_test : -2*sin(pi/24)*cos(73*pi/24)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : 2 * sin(pi / 24) * -cos(73 * pi / 24) = -2*sin(pi/24)*cos(73*pi/24),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -cos(73*pi/24),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/24) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = 2 * sin(pi/24) * cos(pi/24),
{
have : sin(pi/12) = sin(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end




lemma Trigo_391_test (h0 : cos(-2*pi)≠ 0) (h1 : cos((-2)*pi)≠ 0) (h2 : (2*cos(-pi)**2-1)≠ 0) (h3 : (-1+2*cos(-pi)**2)≠ 0) : sin(-2*pi)/(-1 + 2*cos(-pi)**2)=- 1 / tan(179*pi/2):=
begin
have : sin((-2) * pi) / (2 * cos(-pi) ** 2 - 1) = sin(-2*pi)/(-1 + 2*cos(-pi)**2),
{
field_simp at *,
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
have : sin((-2) * pi) / cos((-2) * pi) = sin(-2*pi)/cos(-2*pi),
{
field_simp at *,
},
have : tan(-2*pi) = sin(-2*pi) / cos(-2*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = - 1 / tan(179*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-2*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_392_test (h0 : cos((pi/3)/2)≠ 0) (h1 : sin(pi/3)≠ 0) : (1 - cos(341*pi/3))/sin(pi/3)=sqrt( 3 ) / 3:=
begin
have : cos(pi/3) = cos(341*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (57),
focus{repeat {apply congr_arg _}},
simp,
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_393_test : (-1 + 2*cos(pi/4)**2)**2=cos(pi)/2 + 1/2:=
begin
have : (2 * cos(pi / 4) ** 2 - 1) ** 2 = (-1 + 2*cos(pi/4)**2)**2,
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
have : 1 - (1 / 2 - cos(pi) / 2) = cos(pi)/2 + 1/2,
{
field_simp at *,
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
conv {to_rhs, rw ← this,},
have : cos(pi/2) ** 2 = 1 - sin(pi/2) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_394_test : sin(38*pi)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi)=sqrt( 3 ) / 2:=
begin
have : sin(38 * pi) * cos((-2) * pi / 3) + sin((-2) * pi / 3) * cos(pi) = sin(38*pi)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi),
{
field_simp at *,
},
have : sin(pi) = sin(38*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (19),
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
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_395_test : sin(3*pi/2)*cos(pi/6) + sin(pi/6)*sin(pi)=- sqrt( 3 ) / 2:=
begin
have : cos(pi / 6) * sin(3 * pi / 2) + sin(pi / 6) * sin(pi) = sin(3*pi/2)*cos(pi/6) + sin(pi/6)*sin(pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(3*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) * sin(pi / 6) + cos(pi) * cos(pi / 6) = cos(pi/6)*cos(pi) + sin(pi/6)*sin(pi),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_396_test (h0 : cos(3*pi/2)≠ 0) (h1 : cos(pi)≠ 0) (h2 : (tan(pi)*tan(3*pi/2)+1)≠ 0) (h3 : (1+tan(3*pi/2)*tan(pi))≠ 0) (h4 : cos(3*pi/2)≠ 0) (h5 : cos(pi)≠ 0) (h6 : ((tan(pi)*tan(3*pi/2)+1)*cos(pi)*cos(3*pi/2))≠ 0) (h7 : (cos(3*pi/2)*cos(pi))≠ 0) : sin(pi/2)/((tan(pi)*tan(3*pi/2) + 1)*cos(pi)*cos(3*pi/2))=1 / tan(76*pi):=
begin
have : sin(pi / 2) / (cos(3 * pi / 2) * cos(pi)) / (tan(pi) * tan(3 * pi / 2) + 1) = sin(pi/2)/((tan(pi)*tan(3*pi/2) + 1)*cos(pi)*cos(3*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/2) - tan(pi) = sin(pi/2) / ( cos(3*pi/2) * cos(pi) ),
{
rw tan_sub_tan',
have : sin((3*pi/2) - (pi)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(3 * pi / 2) - tan(pi)) / (1 + tan(3 * pi / 2) * tan(pi)) = (tan(3*pi/2) - tan(pi))/(tan(pi)*tan(3*pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = ( tan(3*pi/2) - tan(pi) ) / ( 1 + tan(3*pi/2) * tan(pi) ),
{
have : tan(pi/2) = tan((3*pi/2) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = 1 / tan(76*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/2) (76),
focus{repeat {apply congr_arg _}},
simp,
},
rw this,
end


lemma Trigo_397_test (h0 : cos(-pi/4)≠ 0) (h1 : (1-tan(-pi/4)**2)≠ 0) (h2 : ((1-1/tan(149*pi/4)**2)*tan(149*pi/4))≠ 0) (h3 : tan(149*pi/4)≠ 0) (h4 : (1-((-1)/tan(149*pi/4))**2)≠ 0) : -2/((1 - 1/tan(149*pi/4)**2)*tan(149*pi/4))=- tan(141*pi/2):=
begin
have : 2 * ((-1) / tan(149 * pi / 4)) / (1 - ((-1) / tan(149 * pi / 4)) ** 2) = -2/((1 - 1/tan(149*pi/4)**2)*tan(149*pi/4)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = -1 / tan(149*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/4) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = 2 * tan(-pi/4) / ( 1 - tan(-pi/4) ** 2 ),
{
have : tan(-pi/2) = tan(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - tan(141*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_398_test : 2*(-1 + 2*cos(3*pi/16)**2)*sin(3*pi/8)=sqrt( 2 ) / 2:=
begin
have : 2 * sin(3 * pi / 8) * (2 * cos(3 * pi / 16) ** 2 - 1) = 2*(-1 + 2*cos(3*pi/16)**2)*sin(3*pi/8),
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




lemma Trigo_400_test : sin(389*pi/4)=- sqrt( 2 ) / 2:=
begin
have : - -sin(389 * pi / 4) = sin(389*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(147*pi/4) = -sin(389*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (147*pi/4) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = -sin(147*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (18),
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


lemma Trigo_401_test : sin(-pi/3) + sin(173*pi)=2 * sin(-7*pi/6) * cos(-5*pi/6):=
begin
have : cos(325*pi/2) = sin(173*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (325*pi/2) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(325 * pi / 2) + sin(-pi / 3) = sin(-pi/3) + cos(325*pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(325*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (80),
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


lemma Trigo_402_test (h0 : tan(-9*pi/2)≠ 0) (h1 : tan((-9)*pi/2)≠ 0) : -1/tan(-9*pi/2)=0:=
begin
have : -(1 / tan((-9) * pi / 2)) = -1/tan(-9*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(37*pi) = 1 / tan(-9*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (37*pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = -tan(37*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (38),
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


lemma Trigo_403_test : -cos(-2*pi)*cos(359*pi/2) + sin(-2*pi)*sin(359*pi/2)=cos(45*pi/2):=
begin
have : -(-sin(359 * pi / 2) * sin((-2) * pi) + cos(359 * pi / 2) * cos((-2) * pi)) = -cos(-2*pi)*cos(359*pi/2) + sin(-2*pi)*sin(359*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(355*pi/2) = -sin(359*pi/2) * sin(-2*pi) + cos(359*pi/2) * cos(-2*pi),
{
have : cos(355*pi/2) = cos((359*pi/2) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(355*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(45*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_404_test : -sin(2*pi)*cos(8*pi/3) + (-4*sin(8*pi/9)**3 + 3*sin(8*pi/9))*cos(2*pi)=sqrt( 3 ) / 2:=
begin
have : -sin(2 * pi) * cos(8 * pi / 3) + ((-4) * sin(8 * pi / 9) ** 3 + 3 * sin(8 * pi / 9)) * cos(2 * pi) = -sin(2*pi)*cos(8*pi/3) + (-4*sin(8*pi/9)**3 + 3*sin(8*pi/9))*cos(2*pi),
{
field_simp at *,
},
have : sin(8*pi/3) = -4 * sin(8*pi/9) ** 3 + 3 * sin(8*pi/9),
{
have : sin(8*pi/3) = sin(3*(8*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8 * pi / 3) * cos(2 * pi) - sin(2 * pi) * cos(8 * pi / 3) = -sin(2*pi)*cos(8*pi/3) + sin(8*pi/3)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(8*pi/3) * cos(2*pi) - sin(2*pi) * cos(8*pi/3),
{
have : sin(2*pi/3) = sin((8*pi/3) - (2*pi)),
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


lemma Trigo_405_test : cos(129*pi)=sin(-pi/6) * cos(pi/3) - sin(pi/3) * cos(-pi/6):=
begin
have : - -cos(129 * pi) = cos(129*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(125*pi/2) = -cos(129*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (125*pi/2) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -sin(125*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-pi/6) * cos(pi/3) - sin(pi/3) * cos(-pi/6),
{
have : sin(-pi/2) = sin((-pi/6) - (pi/3)),
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


lemma Trigo_406_test : sin(243*pi/2)=- cos(52*pi):=
begin
have : sin(103*pi/2) = sin(243*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (103*pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(103*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(52*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_407_test : sin(617*pi/4)*cos(pi/2) + sin(pi/2)*cos(617*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(619*pi/4) = sin(617*pi/4) * cos(pi/2) + sin(pi/2) * cos(617*pi/4),
{
have : sin(619*pi/4) = sin((617*pi/4) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(619*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (3*pi/4) (77),
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


lemma Trigo_408_test : -sin(316*pi/3)=sin(pi/2) * cos(-pi/6) - sin(-pi/6) * cos(pi/2):=
begin
have : sin(253*pi/3) = -sin(316*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (253*pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(253*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(pi/2) * cos(-pi/6) - sin(-pi/6) * cos(pi/2),
{
have : sin(2*pi/3) = sin((pi/2) - (-pi/6)),
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


lemma Trigo_409_test : sin(265*pi/2)*cos(40*pi)=- sin(-pi/2) / 2 + sin(-3*pi/2) / 2:=
begin
have : - -cos(40 * pi) * sin(265 * pi / 2) = sin(265*pi/2)*cos(40*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(40*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) * -sin(265 * pi / 2) = -sin(-pi/2)*sin(265*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(265*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(-pi) = - sin(-pi/2) / 2 + sin(-3*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi) + (-pi/2)) = sin(-3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi) - (-pi/2)) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_410_test (h0 : cos(-pi/6)≠ 0) (h1 : (2*cos(-pi/6))≠ 0) (h2 : (2*(-sin(-pi/12)**2+cos(-pi/12)**2))≠ 0) : sin(-pi/3)/(2*(-sin(-pi/12)**2 + cos(-pi/12)**2))=- sin(377*pi/6):=
begin
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
have : sin(-pi/6) = - sin(377*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_411_test : -3*cos(-pi/9) + 4*cos(-pi/9)**3=-cos(-232*pi/3):=
begin
have : -cos((-232) * pi / 3) = -cos(-232*pi/3),
{
field_simp at *,
},
have : sin(647*pi/6) = cos(-232*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (647*pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : cos(-pi/3) = - sin(647*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_412_test (h0 : sin(4*pi)≠ 0) (h1 : (2*sin(4*pi))≠ 0) (h2 : (4*sin(4*pi))≠ 0) : 1 - cos(2*pi)**2=-sin(8*pi)/(4*sin(4*pi)) + 1/2:=
begin
have : sin(2*pi) ** 2 = 1 - cos(2*pi) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 - sin(8 * pi) / (2 * sin(4 * pi)) / 2 = -sin(8*pi)/(4*sin(4*pi)) + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_413_test : cos(1997*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(1475*pi/12) = cos(1997*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1475*pi/12) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(1475*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (61),
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


lemma Trigo_414_test : -sin(2*pi)*cos(811*pi/12) - sin(811*pi/12)*cos(2*pi)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(sin(811 * pi / 12) * cos(2 * pi) + sin(2 * pi) * cos(811 * pi / 12)) = -sin(2*pi)*cos(811*pi/12) - sin(811*pi/12)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(835*pi/12) = sin(811*pi/12) * cos(2*pi) + sin(2*pi) * cos(811*pi/12),
{
have : sin(835*pi/12) = sin((811*pi/12) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(835*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (34),
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


lemma Trigo_415_test (h0 : sin(-5*pi/6)≠ 0) (h1 : (2*sin((-5)*pi/6))≠ 0) (h2 : (2*sin(-5*pi/6))≠ 0) : sin(-pi)*sin(-5*pi/6) + sin(-5*pi/3)*cos(-pi)/(2*sin(-5*pi/6))=- cos(223*pi/6):=
begin
have : sin(-pi) * sin((-5) * pi / 6) + cos(-pi) * (sin((-5) * pi / 3) / (2 * sin((-5) * pi / 6))) = sin(-pi)*sin(-5*pi/6) + sin(-5*pi/3)*cos(-pi)/(2*sin(-5*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 6) * sin(-pi) + cos((-5) * pi / 6) * cos(-pi) = sin(-pi)*sin(-5*pi/6) + cos(-pi)*cos(-5*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(-5*pi/6) * sin(-pi) + cos(-5*pi/6) * cos(-pi),
{
have : cos(pi/6) = cos((-5*pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - cos(223*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_416_test : sin(91*pi)=sin(45*pi):=
begin
have : - -sin(91 * pi) = sin(91*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi) = -sin(91*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (43*pi) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(43*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(45*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_417_test : (sin(0)*cos(219*pi/2) + cos(0)*cos(-2*pi))*cos(-pi/6)=cos(13*pi/6) / 2 + cos(11*pi/6) / 2:=
begin
have : (sin(0) * cos(219 * pi / 2) + cos(0) * cos((-2) * pi)) * cos(-pi / 6) = (sin(0)*cos(219*pi/2) + cos(0)*cos(-2*pi))*cos(-pi/6),
{
field_simp at *,
},
have : sin(-2*pi) = cos(219*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(0) * sin((-2) * pi) + cos(0) * cos((-2) * pi)) * cos(-pi / 6) = (sin(0)*sin(-2*pi) + cos(0)*cos(-2*pi))*cos(-pi/6),
{
field_simp at *,
},
have : cos(2*pi) = sin(0) * sin(-2*pi) + cos(0) * cos(-2*pi),
{
have : cos(2*pi) = cos((0) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_418_test (h0 : cos(757*pi/6)≠ 0) (h1 : (2*cos(757*pi/6))≠ 0) : -1 + 2*cos(pi/6)**2=sin(757*pi/3)/(2*cos(757*pi/6)):=
begin
have : sin(757*pi/6) = sin(757*pi/3) / ( 2 * cos(757*pi/6) ),
{
have : sin(757*pi/3) = sin(2*(757*pi/6)),
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
have : cos(pi/3) = sin(757*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_419_test : sin(-pi/2)=3*cos(202*pi/3) - 4*cos(202*pi/3)**3:=
begin
have : -(4 * cos(202 * pi / 3) ** 3 - 3 * cos(202 * pi / 3)) = 3*cos(202*pi/3) - 4*cos(202*pi/3)**3,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(202*pi) = 4 * cos(202*pi/3) ** 3 - 3 * cos(202*pi/3),
{
have : cos(202*pi) = cos(3*(202*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : cos(124*pi) = cos(202*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (124*pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = - cos(124*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_420_test : sin(pi/3)*sin(11*pi/6)=sin(64*pi/3)/2 + cos(pi/2)/2:=
begin
have : sin(-pi/6) = sin(11*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 2) / 2 - -sin(64 * pi / 3) / 2 = sin(64*pi/3)/2 + cos(pi/2)/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -sin(64*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) * sin(-pi/6) = cos(pi/2) / 2 - cos(pi/6) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_421_test : -(-4*sin(26*pi/9)**3 + 3*sin(26*pi/9))*sin(pi/2)=cos(5*pi/6) / 2 - cos(pi/6) / 2:=
begin
have : -sin(pi / 2) * ((-4) * sin(26 * pi / 9) ** 3 + 3 * sin(26 * pi / 9)) = -(-4*sin(26*pi/9)**3 + 3*sin(26*pi/9))*sin(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(26*pi/3) = -4 * sin(26*pi/9) ** 3 + 3 * sin(26*pi/9),
{
have : sin(26*pi/3) = sin(3*(26*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 2) * -sin(26 * pi / 3) = -sin(pi/2)*sin(26*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(26*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) * sin(-pi/3) = cos(5*pi/6) / 2 - cos(pi/6) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_422_test : (-3*cos(pi/18) + 4*cos(pi/18)**3)**2=1 - sin(257*pi/6)**2:=
begin
have : sin(pi/6) = sin(257*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (4 * cos(pi / 18) ** 3 - 3 * cos(pi / 18)) ** 2 = (-3*cos(pi/18) + 4*cos(pi/18)**3)**2,
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
have : cos(pi/6) ** 2 = 1 - sin(pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_423_test : -1 + 2*sin(335*pi/12)**2 - sin(-pi/6)=2 * sin(-pi/12) * cos(-pi/4):=
begin
have : -(1 - 2 * sin(335 * pi / 12) ** 2) - sin(-pi / 6) = -1 + 2*sin(335*pi/12)**2 - sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(335*pi/6) = 1 - 2 * sin(335*pi/12) ** 2,
{
have : cos(335*pi/6) = cos(2*(335*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -cos(335*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) - sin(-pi/6) = 2 * sin(-pi/12) * cos(-pi/4),
{
rw sin_sub_sin,
have : cos(((-pi/3) + (-pi/6))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (-pi/6))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_424_test (h0 : cos(pi/4)≠ 0) (h1 : sin(265*pi/4)≠ 0) : sin(pi/4)/sin(265*pi/4)=1:=
begin
have : cos(pi/4) = sin(265*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_425_test (h0 : cos(-11*pi/6)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (tan(-2*pi)*tan(-11*pi/6)+1)≠ 0) (h3 : (1+tan((-11)*pi/6)*tan((-2)*pi))≠ 0) (h4 : cos((-4*pi)/2)≠ 0) (h5 : (1+cos(-4*pi))≠ 0) (h6 : (sin(-4*pi)*tan(-11*pi/6)/(1+cos(-4*pi))+1)≠ 0) (h7 : (1+cos((-4)*pi))≠ 0) (h8 : (sin((-4)*pi)/(1+cos((-4)*pi))*tan((-11)*pi/6)+1)≠ 0) : (-sin(-4*pi)/(1 + cos(-4*pi)) + tan(-11*pi/6))/(sin(-4*pi)*tan(-11*pi/6)/(1 + cos(-4*pi)) + 1)=sqrt( 3 ) / 3:=
begin
have : (-(sin((-4) * pi) / (1 + cos((-4) * pi))) + tan((-11) * pi / 6)) / (sin((-4) * pi) / (1 + cos((-4) * pi)) * tan((-11) * pi / 6) + 1) = (-sin(-4*pi)/(1 + cos(-4*pi)) + tan(-11*pi/6))/(sin(-4*pi)*tan(-11*pi/6)/(1 + cos(-4*pi)) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
have : tan(pi/6) = sqrt( 3 ) / 3,
{
rw tan_pi_div_six,
},
rw this,
end


lemma Trigo_426_test (h0 : sin(-pi/4)≠ 0) (h1 : sin(-pi/4)≠ 0) (h2 : (2*sin(-pi/4))≠ 0) : -sin(404*pi/3) - sin(-pi/6)=sin(-pi/2)*sin(-pi/12)/sin(-pi/4):=
begin
have : sin(-pi/3) = -sin(404*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 12) * (sin(-pi / 2) / (2 * sin(-pi / 4))) = sin(-pi/2)*sin(-pi/12)/sin(-pi/4),
{
field_simp at *,
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
conv {to_rhs, rw ← this,},
have : sin(-pi/3) - sin(-pi/6) = 2 * sin(-pi/12) * cos(-pi/4),
{
rw sin_sub_sin,
have : cos(((-pi/3) + (-pi/6))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/3) - (-pi/6))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_427_test : -(sin(2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(2*pi))**2 + cos(pi/6)**2=1 / 2:=
begin
have : -(sin((-11) * pi / 6) * cos(2 * pi) + sin(2 * pi) * cos((-11) * pi / 6)) ** 2 + cos(pi / 6) ** 2 = -(sin(2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(2*pi))**2 + cos(pi/6)**2,
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


lemma Trigo_428_test : (-3*cos(pi/6) + 4*cos(pi/6)**3)*sin(pi/6)=-sin(-pi/6)*cos(pi/2):=
begin
have : sin(pi / 6) * (4 * cos(pi / 6) ** 3 - 3 * cos(pi / 6)) = (-3*cos(pi/6) + 4*cos(pi/6)**3)*sin(pi/6),
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
have : (-1) / 2 * (2 * sin(-pi / 6) * cos(pi / 2)) = -sin(-pi/6)*cos(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) - sin(2*pi/3) = 2 * sin(-pi/6) * cos(pi/2),
{
rw sin_sub_sin,
have : cos(((pi/3) + (2*pi/3))/2) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (2*pi/3))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -1/2*(sin(pi/3) - sin(2*pi/3)) = -sin(pi/3)/2+sin(2*pi/3)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/6) * cos(pi/2) = - sin(pi/3) / 2 + sin(2*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/2) + (pi/6)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (pi/6)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_429_test (h0 : cos(2*pi)≠ 0) : sin(106*pi)/cos(2*pi)=tan(17*pi):=
begin
have : tan(2*pi) = tan(17*pi),
{
rw tan_eq_tan_add_int_mul_pi (2*pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = sin(106*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (52),
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


lemma Trigo_430_test : -2*(-3*cos(-pi/6) + 4*cos(-pi/6)**3)**2 + cos(-pi/6) + 1=- 2 * sin(5*pi/12) * sin(-7*pi/12):=
begin
have : (-2) * (4 * cos(-pi / 6) ** 3 - 3 * cos(-pi / 6)) ** 2 + cos(-pi / 6) + 1 = -2*(-3*cos(-pi/6) + 4*cos(-pi/6)**3)**2 + cos(-pi/6) + 1,
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
have : cos(-pi / 6) - (2 * cos(-pi / 2) ** 2 - 1) = -2*cos(-pi/2)**2 + cos(-pi/6) + 1,
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
have : cos(-pi/6) - cos(-pi) = - 2 * sin(5*pi/12) * sin(-7*pi/12),
{
rw cos_sub_cos,
have : sin(((-pi/6) + (-pi))/2) = sin(-7*pi/12),
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
ring,
},
rw this,
end


lemma Trigo_431_test : -cos(283*pi/2) + sin(pi/2)=sin(-2*pi) - sin(-pi/2):=
begin
have : sin(-2*pi) = -cos(283*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (-sin(-pi / 2) / 2 + sin((-2) * pi) / 2) = sin(-2*pi) - sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi/4) * cos(-5*pi/4) = -sin(-pi/2) / 2 + sin(-2*pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-5*pi/4) + (-3*pi/4)) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-5*pi/4) - (-3*pi/4)) = sin(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-3*pi/4) * cos(-5*pi/4)) = 2*sin(-3*pi/4)*cos(-5*pi/4),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(-2*pi) + sin(pi/2) = 2 * sin(-3*pi/4) * cos(-5*pi/4),
{
rw sin_add_sin,
have : sin(((-2*pi) + (pi/2))/2) = sin(-3*pi/4),
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
},
rw this,
end


lemma Trigo_432_test : -3*sin(745*pi/6) + 4*sin(745*pi/6)**3=- cos(88*pi):=
begin
have : (-3) * sin(745 * pi / 6) + 4 * sin(745 * pi / 6) ** 3 = -3*sin(745*pi/6) + 4*sin(745*pi/6)**3,
{
field_simp at *,
},
have : cos(pi/3) = sin(745*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (62),
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
have : cos(pi) = - cos(88*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_433_test : -sin(1129*pi/6)=- sin(617*pi/6):=
begin
have : sin(409*pi/6) = sin(1129*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (409*pi/6) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(409*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - sin(617*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_434_test (h0 : sin(199*pi/2)≠ 0) (h1 : (2*sin(199*pi/2))≠ 0) (h2 : (4*sin(199*pi/2)**2)≠ 0) : sin(199*pi)**2/(4*sin(199*pi/2)**2) + sin(pi/2)**2=1:=
begin
have : (sin(199 * pi) / (2 * sin(199 * pi / 2))) ** 2 + sin(pi / 2) ** 2 = sin(199*pi)**2/(4*sin(199*pi/2)**2) + sin(pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(199*pi/2) = sin(199*pi) / ( 2 * sin(199*pi/2) ),
{
have : sin(199*pi) = sin(2*(199*pi/2)),
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
have : sin(pi / 2) ** 2 + (-cos(199 * pi / 2)) ** 2 = cos(199*pi/2)**2 + sin(pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(199*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) ** 2 + cos(pi/2) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_435_test : -cos(-42*pi)=4 * cos(pi/3) ** 3 - 3 * cos(pi/3):=
begin
have : -cos((-42) * pi) = -cos(-42*pi),
{
field_simp at *,
},
have : cos(43*pi) = -cos(-42*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (43*pi) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(43*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (21),
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


lemma Trigo_436_test : sin(397*pi/3)=sqrt( 3 ) / 2:=
begin
have : cos(59*pi/6) = sin(397*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (59*pi/6) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(59*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (4),
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


lemma Trigo_437_test : 1 - 2*sin(2093*pi/12)**2=- sqrt( 3 ) / 2:=
begin
have : sin(5*pi/12) = sin(2093*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi/12) (87),
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


lemma Trigo_438_test (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) (h2 : (1-tan(469*pi/12)**2)≠ 0) : 2*tan(469*pi/12)/(1 - tan(469*pi/12)**2)=sqrt( 3 ) / 3:=
begin
have : tan(pi/12) = tan(469*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (39),
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


lemma Trigo_439_test (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) (h2 : cos(pi)≠ 0) (h3 : (2*cos(pi))≠ 0) (h4 : (4*sin(pi/2)*cos(pi))≠ 0) : -sin(2*pi)/(4*sin(pi/2)*cos(pi)) + cos(-pi/2)=- 2 * sin(-pi/2) * sin(0):=
begin
have : -(sin(2 * pi) / (2 * cos(pi))) / (2 * sin(pi / 2)) + cos(-pi / 2) = -sin(2*pi)/(4*sin(pi/2)*cos(pi)) + cos(-pi/2),
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
have : cos(-pi / 2) - sin(pi) / (2 * sin(pi / 2)) = -sin(pi)/(2*sin(pi/2)) + cos(-pi/2),
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


lemma Trigo_440_test (h0 : cos(-pi/2)≠ 0) (h1 : cos(pi/2)≠ 0) (h2 : (tan(-pi/2)*tan(pi/2)+1)≠ 0) (h3 : (1+tan(-pi/2)*tan(pi/2))≠ 0) (h4 : cos(-pi/2)≠ 0) (h5 : cos(pi/2)≠ 0) (h6 : tan((-pi/2)+(pi/2))≠ 0) (h7 : 1-tan(-pi/2)*tan(pi/2)≠ 0) (h8 : tan(0)≠ 0) (h9 : (2+(-tan(pi/2)-tan(-pi/2))/tan(0))≠ 0) (h10 : (-(tan(-pi/2)+tan(pi/2))/tan(0)+1+1)≠ 0) : (-tan(pi/2) + tan(-pi/2))/(2 + (-tan(pi/2) - tan(-pi/2))/tan(0))=- 1 / tan(99*pi/2):=
begin
have : (-tan(pi / 2) + tan(-pi / 2)) / (-(tan(-pi / 2) + tan(pi / 2)) / tan(0) + 1 + 1) = (-tan(pi/2) + tan(-pi/2))/(2 + (-tan(pi/2) - tan(-pi/2))/tan(0)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) * tan(pi/2) = -( tan(-pi/2) + tan(pi/2) ) / tan(0) + 1,
{
rw tan_mul_tan',
have : tan((-pi/2) + (pi/2)) = tan(0),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-pi/2) * tan(pi/2)) = tan(-pi/2)*tan(pi/2),
{
ring,
},
have : (tan(-pi / 2) - tan(pi / 2)) / (1 + tan(-pi / 2) * tan(pi / 2)) = (-tan(pi/2) + tan(-pi/2))/(tan(-pi/2)*tan(pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = ( tan(-pi/2) - tan(pi/2) ) / ( 1 + tan(-pi/2) * tan(pi/2) ),
{
have : tan(-pi) = tan((-pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - 1 / tan(99*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_441_test : 2*cos(81*pi/4)*cos(89*pi/4)=2 * cos(5*pi/4) * cos(-3*pi/4):=
begin
have : 2 * cos(89 * pi / 4) * cos(81 * pi / 4) = 2*cos(81*pi/4)*cos(89*pi/4),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(85*pi/2) + cos(-2*pi) = 2 * cos(89*pi/4) * cos(81*pi/4),
{
rw cos_add_cos,
have : cos(((85*pi/2) + (-2*pi))/2) = cos(81*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((85*pi/2) - (-2*pi))/2) = cos(89*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(85*pi/2) + cos(-2*pi)) = cos(85*pi/2)+cos(-2*pi),
{
ring,
},
have : cos(85 * pi / 2) + cos((-2) * pi) = cos(85*pi/2) + cos(-2*pi),
{
field_simp at *,
},
have : cos(pi/2) = cos(85*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_442_test : -cos(-2*pi) - 2*sin(-pi/4)**2 + 1=-cos(-2*pi) + cos(-pi/2):=
begin
have : 1 - 2 * sin(-pi / 4) ** 2 - cos((-2) * pi) = -cos(-2*pi) - 2*sin(-pi/4)**2 + 1,
{
field_simp at *,
ring,
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
have : (-2) * (cos((-2) * pi) / 2 - cos(-pi / 2) / 2) = -cos(-2*pi) + cos(-pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/4) * sin(3*pi/4) = cos(-2*pi) / 2 - cos(-pi/2) / 2,
{
rw sin_mul_sin,
have : cos((-5*pi/4) + (3*pi/4)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-5*pi/4) - (3*pi/4)) = cos(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : -2*(sin(-5*pi/4) * sin(3*pi/4)) = -2*sin(3*pi/4)*sin(-5*pi/4),
{
ring,
},
conv {to_rhs, rw this,},
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


lemma Trigo_443_test (h0 : cos(3*pi/2)≠ 0) (h1 : cos(pi/2)≠ 0) (h2 : (tan(pi/2)*tan(3*pi/2)+1)≠ 0) (h3 : (1+tan(3*pi/2)*tan(pi/2))≠ 0) (h4 : (1-tan(pi/2)*tan(21*pi/2))≠ 0) (h5 : (tan(pi/2)*-tan(21*pi/2)+1)≠ 0) : (-tan(pi/2) - tan(21*pi/2))/(1 - tan(pi/2)*tan(21*pi/2))=1 / tan(123*pi/2):=
begin
have : (-tan(pi / 2) + -tan(21 * pi / 2)) / (tan(pi / 2) * -tan(21 * pi / 2) + 1) = (-tan(pi/2) - tan(21*pi/2))/(1 - tan(pi/2)*tan(21*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/2) = -tan(21*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(3 * pi / 2) - tan(pi / 2)) / (1 + tan(3 * pi / 2) * tan(pi / 2)) = (-tan(pi/2) + tan(3*pi/2))/(tan(pi/2)*tan(3*pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(3*pi/2) - tan(pi/2) ) / ( 1 + tan(3*pi/2) * tan(pi/2) ),
{
have : tan(pi) = tan((3*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(123*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_444_test (h0 : sin(pi/2)≠ 0) : -sin(239*pi)=sin(pi) / ( 2 * sin(pi/2) ):=
begin
have : sin(188*pi) = -sin(239*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (188*pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(188*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (94),
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


lemma Trigo_445_test (h0 : sin(203*pi/2)≠ 0) : sin(-pi)/sin(203*pi/2)=-tan(39*pi):=
begin
have : cos(-pi) = sin(203*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = -tan(39*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) / cos(-pi) = tan(-pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_446_test : sin(-5*pi/3)=-sin(-2*pi)*sin(755*pi/6) - sin(pi/3)*sin(15*pi/2):=
begin
have : sin((-2) * pi) * -sin(755 * pi / 6) - sin(pi / 3) * sin(15 * pi / 2) = -sin(-2*pi)*sin(755*pi/6) - sin(pi/3)*sin(15*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -sin(755*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 3) * -sin(15 * pi / 2) + sin((-2) * pi) * cos(pi / 3) = sin(-2*pi)*cos(pi/3) - sin(pi/3)*sin(15*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -sin(15*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/3) = sin(pi/3) * cos(-2*pi) + sin(-2*pi) * cos(pi/3),
{
have : sin(-5*pi/3) = sin((pi/3) + (-2*pi)),
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


lemma Trigo_447_test : -sin(967*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(493*pi/4) = sin(967*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (493*pi/4) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = -cos(493*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (61),
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


lemma Trigo_448_test : -(sin(445*pi/6)*cos(-pi) + sin(-pi)*cos(445*pi/6))*cos(-2*pi)=cos(-5*pi/3) / 2 + cos(-7*pi/3) / 2:=
begin
have : -(sin(445 * pi / 6) * cos(-pi) + sin(-pi) * cos(445 * pi / 6)) * cos((-2) * pi) = -(sin(445*pi/6)*cos(-pi) + sin(-pi)*cos(445*pi/6))*cos(-2*pi),
{
field_simp at *,
},
have : sin(439*pi/6) = sin(445*pi/6) * cos(-pi) + sin(-pi) * cos(445*pi/6),
{
have : sin(439*pi/6) = sin((445*pi/6) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos((-2) * pi) * -sin(439 * pi / 6) = -sin(439*pi/6)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(439*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) * cos(-pi/3) = cos(-5*pi/3) / 2 + cos(-7*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((-2*pi) + (-pi/3)) = cos(-7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (-pi/3)) = cos(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_449_test : -tan(-6*pi)=tan(23*pi):=
begin
have : -tan((-6) * pi) = -tan(-6*pi),
{
field_simp at *,
},
have : tan(53*pi) = -tan(-6*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (53*pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(53*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(23*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_450_test : (-1 + 2*cos(385*pi/12)**2)*sin(-pi/2)=cos(5*pi/6) / 2 - cos(-pi/6) / 2:=
begin
have : sin(-pi / 2) * (2 * cos(385 * pi / 12) ** 2 - 1) = (-1 + 2*cos(385*pi/12)**2)*sin(-pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(385*pi/6) = 2 * cos(385*pi/12) ** 2 - 1,
{
have : cos(385*pi/6) = cos(2*(385*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(385 * pi / 6) * sin(-pi / 2) = sin(-pi/2)*cos(385*pi/6),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(385*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * sin(-pi/2) = cos(5*pi/6) / 2 - cos(-pi/6) / 2,
{
rw sin_mul_sin,
have : cos((pi/3) + (-pi/2)) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (-pi/2)) = cos(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_451_test : -cos(625*pi/6)=-cos(839*pi/6):=
begin
have : sin(85*pi/3) = cos(839*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (85*pi/3) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = -cos(625*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(85*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_452_test : -4*sin(pi/9)**3 + 3*sin(pi/9)=-sin(208*pi/3):=
begin
have : cos(499*pi/6) = sin(208*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (499*pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : sin(pi/3) = - cos(499*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_453_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) (h2 : (4*sin(pi/6)**2)≠ 0) : cos(557*pi/6)**2/(4*sin(pi/6)**2)=1 - sin(pi/6) ** 2:=
begin
have : (-cos(557 * pi / 6)) ** 2 / (4 * sin(pi / 6) ** 2) = cos(557*pi/6)**2/(4*sin(pi/6)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(557*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 3) / (2 * sin(pi / 6))) ** 2 = sin(pi/3)**2/(4*sin(pi/6)**2),
{
field_simp at *,
repeat {left},
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
have : cos(pi/6) ** 2 = 1 - sin(pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_454_test : cos(pi/2)=cos(277*pi/2):=
begin
have : sin(-8*pi) = cos(277*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-8*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin((-8) * pi) = sin(-8*pi),
{
field_simp at *,
},
have : sin(33*pi) = sin(-8*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (33*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(33*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_455_test : -cos(75*pi)=sin(401*pi/2):=
begin
have : sin(205*pi/2) = -cos(75*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (205*pi/2) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(205*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(401*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_456_test : cos(-63*pi/2)=0:=
begin
have : cos((-63) * pi / 2) = cos(-63*pi/2),
{
field_simp at *,
},
have : cos(327*pi/2) = cos(-63*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (327*pi/2) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(327*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (82),
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


lemma Trigo_457_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) (h2 : (2*cos(191*pi/2))≠ 0) (h3 : (2*-cos(191*pi/2))≠ 0) : -sin(pi)/(2*cos(191*pi/2))=1:=
begin
have : sin(pi) / (2 * -cos(191 * pi / 2)) = -sin(pi)/(2*cos(191*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(191*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (47),
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_458_test : -1 + 2*cos(877*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : 2 * cos(877 * pi / 12) ** 2 - 1 = -1 + 2*cos(877*pi/12)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(877*pi/6) = 2 * cos(877*pi/12) ** 2 - 1,
{
have : cos(877*pi/6) = cos(2*(877*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(877*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (73),
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


lemma Trigo_459_test (h0 : cos(-pi/3)≠ 0) (h1 : (4*cos(-pi/3)**2)≠ 0) (h2 : (2*cos(-pi/3))≠ 0) : cos(-2*pi/3)=-sin(247*pi/3)**2/(4*cos(-pi/3)**2) + cos(-pi/3)**2:=
begin
have : -(-sin(247 * pi / 3)) ** 2 / (4 * cos(-pi / 3) ** 2) + cos(-pi / 3) ** 2 = -sin(247*pi/3)**2/(4*cos(-pi/3)**2) + cos(-pi/3)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi/3) = -sin(247*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(sin((-2) * pi / 3) / (2 * cos(-pi / 3))) ** 2 + cos(-pi / 3) ** 2 = -sin(-2*pi/3)**2/(4*cos(-pi/3)**2) + cos(-pi/3)**2,
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


lemma Trigo_460_test : cos(212*pi/3)=- 1 / 2:=
begin
have : cos(86*pi/3) = cos(212*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (86*pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = cos(86*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/3) (14),
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


lemma Trigo_461_test : sin(496*pi/3)=sin(-pi/3) - sin(0):=
begin
have : sin(-pi/3) = sin(496*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (-sin(0) / 2 + sin(-pi / 3) / 2) = sin(-pi/3) - sin(0),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) * cos(-pi/6) = -sin(0) / 2 + sin(-pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/6) + (-pi/6)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (-pi/6)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-pi/6) * cos(-pi/6)) = 2*sin(-pi/6)*cos(-pi/6),
{
ring,
},
conv {to_rhs, rw this,},
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


lemma Trigo_462_test (h0 : tan(196*pi/3)≠ 0) (h1 : tan((-155)*pi/6)≠ 0) (h2 : (1/tan((-155)*pi/6))≠ 0) : -tan(-155*pi/6)=1 / tan(227*pi/3):=
begin
have : (-1) / (1 / tan((-155) * pi / 6)) = -tan(-155*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(196*pi/3) = 1 / tan(-155*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (196*pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(196 * pi / 3) = -1/tan(196*pi/3),
{
field_simp at *,
},
have : tan(-pi/6) = -1 / tan(196*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = 1 / tan(227*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_463_test : -3*sin(205*pi/9) + 4*sin(205*pi/9)**3=2 * sin(-pi/3) * cos(-pi/3):=
begin
have : -((-4) * sin(205 * pi / 9) ** 3 + 3 * sin(205 * pi / 9)) = -3*sin(205*pi/9) + 4*sin(205*pi/9)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(205*pi/3) = -4 * sin(205*pi/9) ** 3 + 3 * sin(205*pi/9),
{
have : sin(205*pi/3) = sin(3*(205*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = -sin(205*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_464_test : cos(-7*pi/6)*cos(-pi/6) - sin(-7*pi/6)*sin(437*pi/6)=- cos(168*pi):=
begin
have : cos((-7) * pi / 6) * cos(-pi / 6) + sin((-7) * pi / 6) * -sin(437 * pi / 6) = cos(-7*pi/6)*cos(-pi/6) - sin(-7*pi/6)*sin(437*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(437*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-7) * pi / 6) * sin(-pi / 6) + cos((-7) * pi / 6) * cos(-pi / 6) = cos(-7*pi/6)*cos(-pi/6) + sin(-7*pi/6)*sin(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(-7*pi/6) * sin(-pi/6) + cos(-7*pi/6) * cos(-pi/6),
{
have : cos(-pi) = cos((-7*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(168*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_465_test : -1 + cos(pi/2) + 2*sin(-pi/6)**2=-2*(-4*sin(pi/36)**3 + 3*sin(pi/36))*sin(5*pi/12):=
begin
have : cos(pi / 2) - (1 - 2 * sin(-pi / 6) ** 2) = -1 + cos(pi/2) + 2*sin(-pi/6)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : (-2) * sin(5 * pi / 12) * ((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) = -2*(-4*sin(pi/36)**3 + 3*sin(pi/36))*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : cos(pi/2) - cos(-pi/3) = - 2 * sin(5*pi/12) * sin(pi/12),
{
rw cos_sub_cos,
have : sin(((pi/2) + (-pi/3))/2) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (-pi/3))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_466_test (h0 : cos((4*pi/3)/2)≠ 0) (h1 : (1+cos(4*pi/3))≠ 0) (h2 : (cos(4*pi/3)+1)≠ 0) (h3 : (sin(pi/3)*sin(-pi)+cos(pi/3)*cos(-pi)+1)≠ 0) (h4 : (cos(-pi)*cos(pi/3)+sin(-pi)*sin(pi/3)+1)≠ 0) : sin(4*pi/3)/(cos(-pi)*cos(pi/3) + sin(-pi)*sin(pi/3) + 1)=- sqrt( 3 ):=
begin
have : sin(4 * pi / 3) / (sin(pi / 3) * sin(-pi) + cos(pi / 3) * cos(-pi) + 1) = sin(4*pi/3)/(cos(-pi)*cos(pi/3) + sin(-pi)*sin(pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/3) = sin(pi/3) * sin(-pi) + cos(pi/3) * cos(-pi),
{
have : cos(4*pi/3) = cos((pi/3) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_467_test : sin(0)=-cos(pi/6)*cos(13*pi/3) - sin(pi/6)*sin(76*pi/3):=
begin
have : -cos(13 * pi / 3) * cos(pi / 6) - sin(pi / 6) * sin(76 * pi / 3) = -cos(pi/6)*cos(13*pi/3) - sin(pi/6)*sin(76*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = -cos(13*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi / 6) * -sin(76 * pi / 3) + sin(-pi / 6) * cos(pi / 6) = sin(-pi/6)*cos(pi/6) - sin(pi/6)*sin(76*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(76*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (12),
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


lemma Trigo_468_test : -4*sin(2*pi/3)**3 + 3*sin(2*pi/3)=-sin(130*pi):=
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
have : cos(61*pi/2) = -sin(130*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (61*pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = cos(61*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_469_test : -cos(-209*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -cos((-209) * pi / 12) = -cos(-209*pi/12),
{
field_simp at *,
},
have : sin(335*pi/12) = cos(-209*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (335*pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(335*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (14),
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


lemma Trigo_470_test : sin(-pi/6)*cos(pi/2) + (-sin(-pi)*cos(-pi/2) + sin(-pi/2)*cos(-pi))*cos(-pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(-pi / 6) * cos(pi / 2) + (sin(-pi / 2) * cos(-pi) - sin(-pi) * cos(-pi / 2)) * cos(-pi / 6) = sin(-pi/6)*cos(pi/2) + (-sin(-pi)*cos(-pi/2) + sin(-pi/2)*cos(-pi))*cos(-pi/6),
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
have : sin(pi/3) = sqrt( 3 ) / 2,
{
rw sin_pi_div_three,
},
rw this,
end


lemma Trigo_471_test : 2*sin(5*pi/12)*sin(2161*pi/12)=1 / 2:=
begin
have : cos(5*pi/12) = sin(2161*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (90),
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


lemma Trigo_472_test (h0 : cos(-pi/6)≠ 0) : sin(503*pi/6)/cos(-pi/6)=1 / tan(212*pi/3):=
begin
have : sin(-pi/6) = sin(503*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = 1 / tan(212*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_473_test : cos(9*pi) - cos(5*pi/2)=2 * sin(pi/4) * cos(-3*pi/4):=
begin
have : sin(-pi) = cos(5*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(9*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) - sin(-pi) = 2 * sin(pi/4) * cos(-3*pi/4),
{
rw sin_sub_sin,
have : cos(((-pi/2) + (-pi))/2) = cos(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/2) - (-pi))/2) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_474_test (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : (3*cos(2*pi/3) - 4*cos(2*pi/3)**3 + 1)/sin(2*pi)=1 / tan(113*pi/2):=
begin
have : (1 - (4 * cos(2 * pi / 3) ** 3 - 3 * cos(2 * pi / 3))) / sin(2 * pi) = (3*cos(2*pi/3) - 4*cos(2*pi/3)**3 + 1)/sin(2*pi),
{
field_simp at *,
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
have : tan(pi) = 1 / tan(113*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_475_test (h0 : sin(410*pi/3)≠ 0) (h1 : (2*sin(410*pi/3))≠ 0) (h2 : (4*sin(410*pi/3)**2)≠ 0) : sin(820*pi/3)**2/(4*sin(410*pi/3)**2)=1 - sin(-pi/3) ** 2:=
begin
have : (sin(820 * pi / 3) / (2 * sin(410 * pi / 3))) ** 2 = sin(820*pi/3)**2/(4*sin(410*pi/3)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(410*pi/3) = sin(820*pi/3) / ( 2 * sin(410*pi/3) ),
{
have : sin(820*pi/3) = sin(2*(410*pi/3)),
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
have : (-cos(410 * pi / 3)) ** 2 = cos(410*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(410*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) ** 2 = 1 - sin(-pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_476_test : cos(1075*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -cos(1075 * pi / 12) = cos(1075*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(551*pi/12) = -cos(1075*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (551*pi/12) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(551*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (23),
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


lemma Trigo_477_test : -sin(pi/12)**2 + sin(403*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : -sin(pi / 12) ** 2 + (-sin(403 * pi / 12)) ** 2 = -sin(pi/12)**2 + sin(403*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(403*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (16),
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_478_test (h0 : cos(57*pi/2)≠ 0) (h1 : (2*cos(57*pi/2))≠ 0) : cos(193*pi)=-sin(57*pi)/(2*cos(57*pi/2)):=
begin
have : -(sin(57 * pi) / (2 * cos(57 * pi / 2))) = -sin(57*pi)/(2*cos(57*pi/2)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(57*pi/2) = sin(57*pi) / ( 2 * cos(57*pi/2) ),
{
have : sin(57*pi) = sin(2*(57*pi/2)),
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
have : sin(-pi/2) = cos(193*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = - sin(57*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_479_test : sin(-pi)=-3*cos(1021*pi/6) + 4*cos(1021*pi/6)**3:=
begin
have : (-3) * cos(1021 * pi / 6) + 4 * cos(1021 * pi / 6) ** 3 = -3*cos(1021*pi/6) + 4*cos(1021*pi/6)**3,
{
field_simp at *,
},
have : cos(131*pi/6) = cos(1021*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (131*pi/6) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 4 * cos(131 * pi / 6) ** 3 - 3 * cos(131 * pi / 6) = -3*cos(131*pi/6) + 4*cos(131*pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(131*pi/2) = 4 * cos(131*pi/6) ** 3 - 3 * cos(131*pi/6),
{
have : cos(131*pi/2) = cos(3*(131*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(131*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_480_test : sin(2*pi)=4*(sin(0)/2 + sin(pi)/2)*cos(pi):=
begin
have : sin(pi/2) * cos(pi/2) = sin(0) / 2 + sin(pi) / 2,
{
rw sin_mul_cos,
have : sin((pi/2) + (pi/2)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (pi/2)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 4*(sin(pi/2) * cos(pi/2))*cos(pi) = 4*sin(pi/2)*cos(pi/2)*cos(pi),
{
ring,
},
conv {to_rhs, rw this,},
have : 2 * (2 * sin(pi / 2) * cos(pi / 2)) * cos(pi) = 4*sin(pi/2)*cos(pi/2)*cos(pi),
{
field_simp at *,
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


lemma Trigo_481_test : -2*sin(pi/4)**2 - cos(1165*pi/6) + 1=- 2 * sin(pi/6) * sin(pi/3):=
begin
have : (-2) * sin(pi / 4) ** 2 - cos(1165 * pi / 6) + 1 = -2*sin(pi/4)**2 - cos(1165*pi/6) + 1,
{
field_simp at *,
},
have : cos(pi/6) = cos(1165*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * sin(pi / 4) ** 2 - cos(pi / 6) = -2*sin(pi/4)**2 - cos(pi/6) + 1,
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
have : cos(pi/2) - cos(pi/6) = - 2 * sin(pi/6) * sin(pi/3),
{
rw cos_sub_cos,
have : sin(((pi/2) + (pi/6))/2) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/2) - (pi/6))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_482_test : cos(281*pi/3)**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : cos(131*pi/3) = cos(281*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (131*pi/3) (25),
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


lemma Trigo_483_test : sin(751*pi/2)**2=1 / 2 - cos(-pi) / 2:=
begin
have : sin(355*pi/2) = sin(751*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (355*pi/2) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(355*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_484_test : sin(509*pi/6)**2=1 - (-1 + 2*cos(-pi/12)**2)**2:=
begin
have : (-sin(509 * pi / 6)) ** 2 = sin(509*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(509*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (2 * cos(-pi / 12) ** 2 - 1) ** 2 = 1 - (-1 + 2*cos(-pi/12)**2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-pi/6) ** 2 = 1 - cos(-pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_485_test : -3*sin(73*pi/18) + 4*sin(73*pi/18)**3=- 1 / 2:=
begin
have : -((-4) * sin(73 * pi / 18) ** 3 + 3 * sin(73 * pi / 18)) = -3*sin(73*pi/18) + 4*sin(73*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(73*pi/6) = -4 * sin(73*pi/18) ** 3 + 3 * sin(73*pi/18),
{
have : sin(73*pi/6) = sin(3*(73*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(73*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (5),
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


lemma Trigo_486_test : cos(pi)=1 - 2*(-4*(sin(2*pi/3)*cos(-pi/2) + sin(-pi/2)*cos(2*pi/3))**3 + 3*sin(2*pi/3)*cos(-pi/2) + 3*sin(-pi/2)*cos(2*pi/3))**2:=
begin
have : 1 - 2 * ((-4) * (sin(2 * pi / 3) * cos(-pi / 2) + sin(-pi / 2) * cos(2 * pi / 3)) ** 3 + 3 * (sin(2 * pi / 3) * cos(-pi / 2) + sin(-pi / 2) * cos(2 * pi / 3))) ** 2 = 1 - 2*(-4*(sin(2*pi/3)*cos(-pi/2) + sin(-pi/2)*cos(2*pi/3))**3 + 3*sin(2*pi/3)*cos(-pi/2) + 3*sin(-pi/2)*cos(2*pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_487_test : sin(-2*pi)*cos(176*pi/3) + sin(-5*pi/3)*cos(-2*pi)=sqrt( 3 ) / 2:=
begin
have : -sin((-2) * pi) * -cos(176 * pi / 3) + sin((-5) * pi / 3) * cos((-2) * pi) = sin(-2*pi)*cos(176*pi/3) + sin(-5*pi/3)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/3) = -cos(176*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-5*pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 3) * cos((-2) * pi) - sin((-2) * pi) * cos((-5) * pi / 3) = -sin(-2*pi)*cos(-5*pi/3) + sin(-5*pi/3)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(-5*pi/3) * cos(-2*pi) - sin(-2*pi) * cos(-5*pi/3),
{
have : sin(pi/3) = sin((-5*pi/3) - (-2*pi)),
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


lemma Trigo_488_test : 2*sin(-pi)*sin(151*pi/2)*cos(pi/6)=sin(-13*pi/6) / 2 + sin(-11*pi/6) / 2:=
begin
have : cos(-pi) = sin(151*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (38),
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
have : sin(-2*pi) * cos(pi/6) = sin(-13*pi/6) / 2 + sin(-11*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (pi/6)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi/6)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_489_test (h0 : tan(1015*pi/12)≠ 0) (h1 : sin(1015*pi/12)≠ 0) (h2 : (sin(1015*pi/12)/cos(1015*pi/12))≠ 0) (h3 : cos(1015*pi/12)≠ 0) : -cos(1015*pi/12)/sin(1015*pi/12)=2 - sqrt( 3 ):=
begin
have : (-1) / (sin(1015 * pi / 12) / cos(1015 * pi / 12)) = -cos(1015*pi/12)/sin(1015*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1015*pi/12) = sin(1015*pi/12) / cos(1015*pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(1015 * pi / 12) = -1/tan(1015*pi/12),
{
field_simp at *,
},
have : tan(pi/12) = -1 / tan(1015*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/12) (84),
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


lemma Trigo_490_test : cos(62*pi)=1 - 2*cos(77*pi/2)**2:=
begin
have : cos(-4*pi) = cos(62*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-4*pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (-cos(77 * pi / 2)) ** 2 = 1 - 2*cos(77*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = -cos(77*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (20),
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


lemma Trigo_491_test (h0 : cos(122*pi/3)≠ 0) (h1 : cos(pi)≠ 0) (h2 : (1+tan(122*pi/3)*tan(pi))≠ 0) (h3 : (tan(pi)*tan(122*pi/3)+1)≠ 0) : (tan(122*pi/3) - tan(pi))/(tan(pi)*tan(122*pi/3) + 1)=- sqrt( 3 ):=
begin
have : (tan(122 * pi / 3) - tan(pi)) / (1 + tan(122 * pi / 3) * tan(pi)) = (tan(122*pi/3) - tan(pi))/(tan(pi)*tan(122*pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(119*pi/3) = ( tan(122*pi/3) - tan(pi) ) / ( 1 + tan(122*pi/3) * tan(pi) ),
{
have : tan(119*pi/3) = tan((122*pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = tan(119*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (2*pi/3) (39),
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


lemma Trigo_492_test : -3*cos(101*pi/3) + 4*cos(101*pi/3)**3=- sin(369*pi/2):=
begin
have : 3 * -cos(101 * pi / 3) - 4 * (-cos(101 * pi / 3)) ** 3 = -3*cos(101*pi/3) + 4*cos(101*pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(101*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(-pi/2) = - sin(369*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/2) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_493_test : sin(619*pi/6)*cos(2*pi) + sin(2*pi)*cos(619*pi/6)=sin(655*pi/6):=
begin
have : sin(631*pi/6) = sin(619*pi/6) * cos(2*pi) + sin(2*pi) * cos(619*pi/6),
{
have : sin(631*pi/6) = sin((619*pi/6) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(631*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(655*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_494_test (h0 : cos((pi/6)/2)≠ 0) (h1 : (cos(pi/6)+1)≠ 0) (h2 : (1+cos(pi/6))≠ 0) : (sin(0)*cos(-pi/6) - sin(-pi/6)*cos(0))/(cos(pi/6) + 1)=2 - sqrt( 3 ):=
begin
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


lemma Trigo_495_test : sin(-241*pi/2)=- 1:=
begin
have : sin((-241) * pi / 2) = sin(-241*pi/2),
{
field_simp at *,
},
have : sin(243*pi/2) = sin(-241*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (243*pi/2) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(243*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (60),
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


lemma Trigo_496_test : -sin(323*pi/3)=-sin(35*pi)*cos(-pi/3) + sin(-pi/2)*sin(-pi/3):=
begin
have : sin(-pi / 2) * sin(-pi / 3) + -sin(35 * pi) * cos(-pi / 3) = -sin(35*pi)*cos(-pi/3) + sin(-pi/2)*sin(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -sin(35*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = -sin(323*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(-pi/2) * sin(-pi/3) + cos(-pi/2) * cos(-pi/3),
{
have : cos(-pi/6) = cos((-pi/2) - (-pi/3)),
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


lemma Trigo_497_test (h0 : cos((2*pi)/2)≠ 0) (h1 : (1+cos(2*pi))≠ 0) (h2 : (1+cos(190*pi))≠ 0) : sin(2*pi)/(1 + cos(190*pi))=0:=
begin
have : cos(2*pi) = cos(190*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (96),
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


lemma Trigo_498_test : -4*sin(5*pi/24)**2*cos(5*pi/24)**2 + cos(5*pi/12)**2=- sqrt( 3 ) / 2:=
begin
have : -(2 * sin(5 * pi / 24) * cos(5 * pi / 24)) ** 2 + cos(5 * pi / 12) ** 2 = -4*sin(5*pi/24)**2*cos(5*pi/24)**2 + cos(5*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = 2 * sin(5*pi/24) * cos(5*pi/24),
{
have : sin(5*pi/12) = sin(2*(5*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
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
have : cos(5*pi/6) = - sqrt( 3 ) / 2,
{
rw cos_five_pi_div_six,
},
rw this,
end


lemma Trigo_499_test : sin(115*pi/2)=- 1:=
begin
have : - -sin(115 * pi / 2) = sin(115*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(122*pi) = -sin(115*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (122*pi) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(122*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (61),
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


lemma Trigo_500_test : (-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(5*pi/6) + sin(-pi/3)*cos(5*pi/6)=- sin(391*pi/2):=
begin
have : sin(5 * pi / 6) * (-sin(-pi / 6) ** 2 + cos(-pi / 6) ** 2) + sin(-pi / 3) * cos(5 * pi / 6) = (-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(5*pi/6) + sin(-pi/3)*cos(5*pi/6),
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
have : sin(pi/2) = sin(5*pi/6) * cos(-pi/3) + sin(-pi/3) * cos(5*pi/6),
{
have : sin(pi/2) = sin((5*pi/6) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_501_test (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) (h2 : (4*sin(pi/4)*cos(pi/4))≠ 0) (h3 : (2*(2*sin(pi/4)*cos(pi/4)))≠ 0) : sin(pi)/(4*sin(pi/4)*cos(pi/4))=0:=
begin
have : sin(pi) / (2 * (2 * sin(pi / 4) * cos(pi / 4))) = sin(pi)/(4*sin(pi/4)*cos(pi/4)),
{
field_simp at *,
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


lemma Trigo_502_test : (1 - 2*sin(-pi/12)**2)*sin(69*pi/2)=cos(-13*pi/6) / 2 + cos(11*pi/6) / 2:=
begin
have : cos(2*pi) = sin(69*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (16),
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
have : cos(-pi/6) * cos(2*pi) = cos(-13*pi/6) / 2 + cos(11*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (2*pi)) = cos(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (2*pi)) = cos(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_503_test (h0 : cos(pi/3)≠ 0) : tan(pi/3)=- 1 / tan(605*pi/6):=
begin
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/3) / cos(pi/3)) = sin(pi/3)/cos(pi/3),
{
ring,
},
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = - 1 / tan(605*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_504_test : -sin(1139*pi/6)=sin(229*pi/6):=
begin
have : cos(14*pi/3) = sin(1139*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (14*pi/3) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(14*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(229*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_505_test (h0 : cos(-pi/6)≠ 0) : (sin(-7*pi/6)*cos(-pi) - sin(-pi)*cos(-7*pi/6))/cos(-pi/6)=- tan(55*pi/6):=
begin
have : (sin((-7) * pi / 6) * cos(-pi) - sin(-pi) * cos((-7) * pi / 6)) / cos(-pi / 6) = (sin(-7*pi/6)*cos(-pi) - sin(-pi)*cos(-7*pi/6))/cos(-pi/6),
{
field_simp at *,
},
have : sin(-pi/6) = sin(-7*pi/6) * cos(-pi) - sin(-pi) * cos(-7*pi/6),
{
have : sin(-pi/6) = sin((-7*pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - tan(55*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_506_test : -sin(-293*pi/4)=- sqrt( 2 ) / 2:=
begin
have : -sin((-293) * pi / 4) = -sin(-293*pi/4),
{
field_simp at *,
},
have : cos(371*pi/4) = -sin(-293*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (371*pi/4) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = cos(371*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi/4) (46),
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


lemma Trigo_507_test : -sin(pi/2)*cos(851*pi/6) + sin(851*pi/6)*cos(pi/2)=2 * sin(-pi/3) * cos(-pi/3):=
begin
have : sin(851 * pi / 6) * cos(pi / 2) - sin(pi / 2) * cos(851 * pi / 6) = -sin(pi/2)*cos(851*pi/6) + sin(851*pi/6)*cos(pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(424*pi/3) = sin(851*pi/6) * cos(pi/2) - sin(pi/2) * cos(851*pi/6),
{
have : sin(424*pi/3) = sin((851*pi/6) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = sin(424*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_508_test : cos(574*pi/3)/2 + sin(-11*pi/6)/2=- sin(11*pi/6) / 2 + sin(-13*pi/6) / 2:=
begin
have : cos(574 * pi / 3) / 2 + sin((-11) * pi / 6) / 2 = cos(574*pi/3)/2 + sin(-11*pi/6)/2,
{
field_simp at *,
},
have : sin(-13*pi/6) = cos(574*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-13*pi/6) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-11) * pi / 6) / 2 + sin((-13) * pi / 6) / 2 = sin(-13*pi/6)/2 + sin(-11*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(-pi/6) = sin(-11*pi/6) / 2 + sin(-13*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-pi/6)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-pi/6)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(-2*pi) * cos(-pi/6)) = sin(-2*pi)*cos(-pi/6),
{
ring,
},
have : sin(-2*pi) * cos(-pi/6) = - sin(11*pi/6) / 2 + sin(-13*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/6) + (-2*pi)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/6) - (-2*pi)) = sin(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_509_test : -(-sin(pi/6)*cos(13*pi/24) + sin(13*pi/24)*cos(pi/6))**2 + cos(3*pi/8)**2=- sqrt( 2 ) / 2:=
begin
have : -(sin(13 * pi / 24) * cos(pi / 6) - sin(pi / 6) * cos(13 * pi / 24)) ** 2 + cos(3 * pi / 8) ** 2 = -(-sin(pi/6)*cos(13*pi/24) + sin(13*pi/24)*cos(pi/6))**2 + cos(3*pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/8) = sin(13*pi/24) * cos(pi/6) - sin(pi/6) * cos(13*pi/24),
{
have : sin(3*pi/8) = sin((13*pi/24) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
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


lemma Trigo_510_test : sin(31*pi)=cos(681*pi/2):=
begin
have : sin(-2*pi) = sin(31*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos(681 * pi / 2) = cos(681*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(391*pi/2) = -cos(681*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (391*pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = - cos(391*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_511_test : (1 - 2*sin(pi/6)**2)**2=1/2 - cos(245*pi/3)/2:=
begin
have : -cos(245 * pi / 3) / 2 + 1 / 2 = 1/2 - cos(245*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/3) = -cos(245*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi/3) (40),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_512_test (h0 : sin(pi/3)≠ 0) (h1 : (2*sin(pi/3))≠ 0) : sin(2*pi/3)/(2*sin(pi/3))=cos(pi/2)*cos(535*pi/6) - sin(pi/2)*sin(535*pi/6):=
begin
have : -sin(535 * pi / 6) * sin(pi / 2) + cos(535 * pi / 6) * cos(pi / 2) = cos(pi/2)*cos(535*pi/6) - sin(pi/2)*sin(535*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(269*pi/3) = -sin(535*pi/6) * sin(pi/2) + cos(535*pi/6) * cos(pi/2),
{
have : cos(269*pi/3) = cos((535*pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(269*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_513_test : 2*sin(227*pi/4)*cos(227*pi/4)=- 1:=
begin
have : sin(227*pi/2) = 2 * sin(227*pi/4) * cos(227*pi/4),
{
have : sin(227*pi/2) = sin(2*(227*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(227*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (57),
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


lemma Trigo_514_test : 2*sin(353*pi/12)*cos(353*pi/12)=cos(601*pi/3):=
begin
have : sin(353*pi/6) = 2 * sin(353*pi/12) * cos(353*pi/12),
{
have : sin(353*pi/6) = sin(2*(353*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(353*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(601*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_515_test : -cos(-110*pi/3)=cos(553*pi/3):=
begin
have : -cos((-110) * pi / 3) = -cos(-110*pi/3),
{
field_simp at *,
},
have : cos(461*pi/3) = -cos(-110*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (461*pi/3) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(461*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(553*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_516_test (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) (h2 : (2*cos(174*pi))≠ 0) (h3 : (2*-cos(174*pi))≠ 0) : -sin(2*pi)/(2*cos(174*pi))=- sin(39*pi):=
begin
have : sin(2 * pi) / (2 * -cos(174 * pi)) = -sin(2*pi)/(2*cos(174*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(174*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (87),
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
have : sin(pi) = - sin(39*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_517_test (h0 : tan(49*pi)≠ 0) (h1 : cos(49*pi)≠ 0) (h2 : sin(49*pi)≠ 0) (h3 : (sin(49*pi)/cos(49*pi))≠ 0) : -cos(49*pi)/sin(49*pi)=- 1 / tan(29*pi):=
begin
have : (-1) / (sin(49 * pi) / cos(49 * pi)) = -cos(49*pi)/sin(49*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(49*pi) = sin(49*pi) / cos(49*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(49 * pi) = -1/tan(49*pi),
{
field_simp at *,
},
have : tan(-pi/2) = -1 / tan(49*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - 1 / tan(29*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_519_test (h0 : cos(81*pi)≠ 0) : sin(81*pi)/cos(81*pi)=0:=
begin
have : tan(81*pi) = sin(81*pi) / cos(81*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = tan(81*pi),
{
rw tan_eq_tan_add_int_mul_pi (pi) (80),
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


lemma Trigo_520_test (h0 : cos(-pi/3)≠ 0) (h1 : (2*cos(-pi/3))≠ 0) (h2 : (2*sin(973*pi/6))≠ 0) : sin(-2*pi/3)/(2*sin(973*pi/6))=sin(412*pi/3):=
begin
have : sin((-2) * pi / 3) / (2 * sin(973 * pi / 6)) = sin(-2*pi/3)/(2*sin(973*pi/6)),
{
field_simp at *,
},
have : cos(-pi/3) = sin(973*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi / 3) / (2 * cos(-pi / 3)) = sin(-2*pi/3)/(2*cos(-pi/3)),
{
field_simp at *,
},
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
have : sin(-pi/3) = sin(412*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_521_test : 4*cos(179*pi/4)**3 - 3*cos(179*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(537*pi/4) = 4 * cos(179*pi/4) ** 3 - 3 * cos(179*pi/4),
{
have : cos(537*pi/4) = cos(3*(179*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(537*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (67),
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


lemma Trigo_522_test : sin(pi/3)=-1 + 2*(cos(-pi)*cos(839*pi/12) + sin(-pi)*sin(839*pi/12))**2:=
begin
have : -1 + 2 * (sin(839 * pi / 12) * sin(-pi) + cos(839 * pi / 12) * cos(-pi)) ** 2 = -1 + 2*(cos(-pi)*cos(839*pi/12) + sin(-pi)*sin(839*pi/12))**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(851*pi/12) = sin(839*pi/12) * sin(-pi) + cos(839*pi/12) * cos(-pi),
{
have : cos(851*pi/12) = cos((839*pi/12) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * cos(851 * pi / 12) ** 2 - 1 = -1 + 2*cos(851*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(851*pi/6) = 2 * cos(851*pi/12) ** 2 - 1,
{
have : cos(851*pi/6) = cos(2*(851*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = cos(851*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_523_test : sin(298*pi/3) + sin(pi/6)=2 * sin(-pi/12) * cos(pi/4):=
begin
have : sin(29*pi/3) = sin(298*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (29*pi/3) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) + sin(29 * pi / 3) = sin(29*pi/3) + sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(29*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (5),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_524_test : 4*cos(1171*pi/36)**3 - 3*cos(1171*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-4) * (-cos(1171 * pi / 36)) ** 3 + 3 * -cos(1171 * pi / 36) = 4*cos(1171*pi/36)**3 - 3*cos(1171*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) = -cos(1171*pi/36),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/36) (16),
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


lemma Trigo_525_test (h0 : sin(5*pi/12)≠ 0) (h1 : (2*sin(5*pi/12))≠ 0) : -sin(-pi/3)*sin(5*pi/6)/(2*sin(5*pi/12)) + sin(5*pi/12)*cos(-pi/3)=sqrt( 2 ) / 2:=
begin
have : -sin(-pi / 3) * (sin(5 * pi / 6) / (2 * sin(5 * pi / 12))) + sin(5 * pi / 12) * cos(-pi / 3) = -sin(-pi/3)*sin(5*pi/6)/(2*sin(5*pi/12)) + sin(5*pi/12)*cos(-pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(5*pi/6) / ( 2 * sin(5*pi/12) ),
{
have : sin(5*pi/6) = sin(2*(5*pi/12)),
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


lemma Trigo_526_test : sin(356*pi/3)**2=1 - sin(643*pi/6)**2:=
begin
have : 1 - (-sin(643 * pi / 6)) ** 2 = 1 - sin(643*pi/6)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -sin(643*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (-sin(356 * pi / 3)) ** 2 = sin(356*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(356*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (59),
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


lemma Trigo_527_test (h0 : sin(198*pi)≠ 0) (h1 : (2*sin(198*pi))≠ 0) : -sin(396*pi)/(2*sin(198*pi))=- 1:=
begin
have : -(sin(396 * pi) / (2 * sin(198 * pi))) = -sin(396*pi)/(2*sin(198*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(198*pi) = sin(396*pi) / ( 2 * sin(198*pi) ),
{
have : sin(396*pi) = sin(2*(198*pi)),
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
have : cos(pi) = -cos(198*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (98),
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


lemma Trigo_528_test : sin(90*pi)*cos(2*pi) + sin(2*pi)*cos(90*pi)=- 4 * sin(-pi) ** 3 + 3 * sin(-pi):=
begin
have : sin(92*pi) = sin(90*pi) * cos(2*pi) + sin(2*pi) * cos(90*pi),
{
have : sin(92*pi) = sin((90*pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi) = sin(92*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-3*pi) (44),
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


lemma Trigo_529_test : -(-3*cos(-5*pi/12) + 4*cos(-5*pi/12)**3)*sin(-2*pi) + sin(-5*pi/4)*cos(-2*pi)=sqrt( 2 ) / 2:=
begin
have : -sin((-2) * pi) * (4 * cos((-5) * pi / 12) ** 3 - 3 * cos((-5) * pi / 12)) + sin((-5) * pi / 4) * cos((-2) * pi) = -(-3*cos(-5*pi/12) + 4*cos(-5*pi/12)**3)*sin(-2*pi) + sin(-5*pi/4)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/4) = 4 * cos(-5*pi/12) ** 3 - 3 * cos(-5*pi/12),
{
have : cos(-5*pi/4) = cos(3*(-5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 4) * cos((-2) * pi) - sin((-2) * pi) * cos((-5) * pi / 4) = -sin(-2*pi)*cos(-5*pi/4) + sin(-5*pi/4)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(-5*pi/4) * cos(-2*pi) - sin(-2*pi) * cos(-5*pi/4),
{
have : sin(3*pi/4) = sin((-5*pi/4) - (-2*pi)),
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


lemma Trigo_530_test (h0 : tan(47*pi/2)≠ 0) (h1 : -tan(5*pi/2)≠ 0) (h2 : tan(5*pi/2)≠ 0) : 1/tan(5*pi/2)=1 / tan(79*pi/2):=
begin
have : (-1) / -tan(5 * pi / 2) = 1/tan(5*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(47*pi/2) = -tan(5*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (47*pi/2) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(47 * pi / 2) = -1/tan(47*pi/2),
{
field_simp at *,
},
have : tan(2*pi) = -1 / tan(47*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (2*pi) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = 1 / tan(79*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_531_test : cos(113*pi/2) + cos(341*pi/3)=2 * cos(5*pi/12) * cos(-pi/12):=
begin
have : cos(pi/3) = cos(341*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 3) + cos(113 * pi / 2) = cos(113*pi/2) + cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(113*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (28),
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


lemma Trigo_532_test : -sin(68*pi/3)=sin(pi/3)*cos(-pi) + (cos(-pi/6)*cos(pi/2) - sin(-pi/6)*sin(pi/2))*sin(-pi):=
begin
have : sin(-2*pi/3) = -sin(68*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi/3) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) * cos(-pi) + sin(-pi) * (-sin(pi / 2) * sin(-pi / 6) + cos(pi / 2) * cos(-pi / 6)) = sin(pi/3)*cos(-pi) + (cos(-pi/6)*cos(pi/2) - sin(-pi/6)*sin(pi/2))*sin(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_533_test : 1/2 - cos(pi/3)/2=cos(226*pi/3)/2 + 1/2:=
begin
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
conv {to_lhs, rw ← this,},
have : 1 / 2 - -cos(226 * pi / 3) / 2 = cos(226*pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(226*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_534_test : -cos(1051*pi/6)=-cos(1493*pi/6):=
begin
have : sin(232*pi/3) = cos(1493*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (232*pi/3) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = -cos(1051*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(232*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_535_test : -cos(47*pi/4)**2 + sin(47*pi/4)**2=- sin(130*pi):=
begin
have : -(-sin(47 * pi / 4) ** 2 + cos(47 * pi / 4) ** 2) = -cos(47*pi/4)**2 + sin(47*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(47*pi/2) = -sin(47*pi/4) ** 2 + cos(47*pi/4) ** 2,
{
have : cos(47*pi/2) = cos(2*(47*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(47*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(130*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_536_test : -sin(123*pi/2)**2 + cos(-pi/2)**2=- sin(29*pi/2):=
begin
have : sin(-pi/2) = sin(123*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(-pi/2) ** 2 + cos(-pi/2) ** 2,
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
conv {to_lhs, rw ← this,},
have : cos(-pi) = - sin(29*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_537_test (h0 : cos((2*pi)/2)≠ 0) (h1 : sin(2*pi)≠ 0) : (sin(299*pi/2) + 1)/sin(2*pi)=0:=
begin
have : (1 - -sin(299 * pi / 2)) / sin(2 * pi) = (sin(299*pi/2) + 1)/sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = -sin(299*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (73),
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


lemma Trigo_538_test : -tan(-385*pi/12)=2 - sqrt( 3 ):=
begin
have : -tan((-385) * pi / 12) = -tan(-385*pi/12),
{
field_simp at *,
},
have : tan(445*pi/12) = -tan(-385*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (445*pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = tan(445*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (37),
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


lemma Trigo_539_test (h0 : cos((2*pi)/2)≠ 0) (h1 : (1+cos(2*pi))≠ 0) : sin(127*pi)/(1 + cos(2*pi))=0:=
begin
have : sin(2*pi) = sin(127*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi) (64),
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


lemma Trigo_540_test (h0 : cos(-pi/18)≠ 0) (h1 : (2*cos(-pi/18)**3)≠ 0) (h2 : (2*cos(-pi/18))≠ 0) : 3*sin(-pi/9)/(2*cos(-pi/18)) - sin(-pi/9)**3/(2*cos(-pi/18)**3)=sin(pi/6) * cos(-pi/3) + sin(-pi/3) * cos(pi/6):=
begin
have : 3 * (sin(-pi / 9) / (2 * cos(-pi / 18))) - 4 * (sin(-pi / 9) / (2 * cos(-pi / 18))) ** 3 = 3*sin(-pi/9)/(2*cos(-pi/18)) - sin(-pi/9)**3/(2*cos(-pi/18)**3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/18) = sin(-pi/9) / ( 2 * cos(-pi/18) ),
{
have : sin(-pi/9) = sin(2*(-pi/18)),
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
have : sin(-pi/6) = sin(pi/6) * cos(-pi/3) + sin(-pi/3) * cos(pi/6),
{
have : sin(-pi/6) = sin((pi/6) + (-pi/3)),
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


lemma Trigo_541_test : -cos(157*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(119*pi/6) = cos(157*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (119*pi/6) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -cos(119*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/6) (9),
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


lemma Trigo_542_test : cos(-517*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos((-517) * pi / 6) = cos(-517*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1135*pi/6) = -cos(-517*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (1135*pi/6) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -cos(1135*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (94),
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


lemma Trigo_543_test (h0 : cos((2*pi)/2)≠ 0) (h1 : (1+cos(2*pi))≠ 0) (h2 : (1+sin(197*pi/2))≠ 0) : sin(2*pi)/(1 + sin(197*pi/2))=0:=
begin
have : cos(2*pi) = sin(197*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (50),
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


lemma Trigo_544_test (h0 : cos(-pi/3)≠ 0) (h1 : cos((-2*pi/3)/2)≠ 0) (h2 : sin(-2*pi/3)≠ 0) (h3 : sin((-2)*pi/3)≠ 0) : (1 - cos(-2*pi/3))/sin(-2*pi/3)=cos(1015*pi/6)/cos(-pi/3):=
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
have : sin(-pi/3) = cos(1015*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(-pi/3) = sin(-pi/3) / cos(-pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_545_test : -sin(-pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi/2) + sin(pi/3)=sin(-pi/3) + sin(pi/3):=
begin
have : sin(pi / 3) + (sin((-5) * pi / 6) * cos(-pi / 2) - sin(-pi / 2) * cos((-5) * pi / 6)) = -sin(-pi/2)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi/2) + sin(pi/3),
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
have : 2 * (sin(-pi / 3) / 2 + sin(pi / 3) / 2) = sin(-pi/3) + sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(0) * cos(pi/3) = sin(-pi/3) / 2 + sin(pi/3) / 2,
{
rw sin_mul_cos,
have : sin((0) + (pi/3)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((0) - (pi/3)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(0) * cos(pi/3)) = 2*sin(0)*cos(pi/3),
{
ring,
},
conv {to_rhs, rw this,},
have : sin(pi/3) + sin(-pi/3) = 2 * sin(0) * cos(pi/3),
{
rw sin_add_sin,
have : sin(((pi/3) + (-pi/3))/2) = sin(0),
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
},
rw this,
end


lemma Trigo_546_test : sin(5*pi/6)*cos(pi/6) + sin(pi/6)*sin(80*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(5 * pi / 6) * cos(pi / 6) - sin(pi / 6) * -sin(80 * pi / 3) = sin(5*pi/6)*cos(pi/6) + sin(pi/6)*sin(80*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(80*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(5*pi/6) * cos(pi/6) - sin(pi/6) * cos(5*pi/6),
{
have : sin(2*pi/3) = sin((5*pi/6) - (pi/6)),
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


lemma Trigo_547_test : -1 + 2*(cos(pi)*cos(25*pi/12) + sin(pi)*sin(25*pi/12))**2=- sin(2*pi) * sin(pi/6) + cos(2*pi) * cos(pi/6):=
begin
have : -1 + 2 * (sin(25 * pi / 12) * sin(pi) + cos(25 * pi / 12) * cos(pi)) ** 2 = -1 + 2*(cos(pi)*cos(25*pi/12) + sin(pi)*sin(25*pi/12))**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/12) = sin(25*pi/12) * sin(pi) + cos(25*pi/12) * cos(pi),
{
have : cos(13*pi/12) = cos((25*pi/12) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(13 * pi / 12) ** 2 - 1 = -1 + 2*cos(13*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/6) = 2 * cos(13*pi/12) ** 2 - 1,
{
have : cos(13*pi/6) = cos(2*(13*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
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


lemma Trigo_548_test : sin(-22*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin((-22) * pi / 3) = sin(-22*pi/3),
{
field_simp at *,
},
have : cos(911*pi/6) = sin(-22*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (911*pi/6) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = cos(911*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (75),
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




lemma Trigo_550_test (h0 : cos((2*pi)/2)≠ 0) (h1 : (1+cos(2*pi))≠ 0) : cos(387*pi/2)/(1 + cos(2*pi))=0:=
begin
have : sin(2*pi) = cos(387*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (95),
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


lemma Trigo_551_test (h0 : cos(269*pi/6)≠ 0) (h1 : cos(-pi/6)≠ 0) (h2 : (1+tan(269*pi/6)*tan(-pi/6))≠ 0) (h3 : (tan(-pi/6)*tan(269*pi/6)+1)≠ 0) : -(tan(269*pi/6) - tan(-pi/6))/(tan(-pi/6)*tan(269*pi/6) + 1)=- tan(41*pi):=
begin
have : -((tan(269 * pi / 6) - tan(-pi / 6)) / (1 + tan(269 * pi / 6) * tan(-pi / 6))) = -(tan(269*pi/6) - tan(-pi/6))/(tan(-pi/6)*tan(269*pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(45*pi) = ( tan(269*pi/6) - tan(-pi/6) ) / ( 1 + tan(269*pi/6) * tan(-pi/6) ),
{
have : tan(45*pi) = tan((269*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = -tan(45*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = - tan(41*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_552_test (h0 : sin(538*pi/3)≠ 0) (h1 : (2*sin(538*pi/3))≠ 0) : sin(1076*pi/3)/(2*sin(538*pi/3))=- 1 / 2:=
begin
have : cos(538*pi/3) = sin(1076*pi/3) / ( 2 * sin(538*pi/3) ),
{
have : sin(1076*pi/3) = sin(2*(538*pi/3)),
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
have : cos(2*pi/3) = cos(538*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (90),
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


lemma Trigo_553_test : -cos(pi/6)*cos(7*pi/3) + sin(pi/6)*sin(7*pi/3)=4 * cos(-pi/2) ** 3 - 3 * cos(-pi/2):=
begin
have : -(-sin(7 * pi / 3) * sin(pi / 6) + cos(7 * pi / 3) * cos(pi / 6)) = -cos(pi/6)*cos(7*pi/3) + sin(pi/6)*sin(7*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/2) = -sin(7*pi/3) * sin(pi/6) + cos(7*pi/3) * cos(pi/6),
{
have : cos(5*pi/2) = cos((7*pi/3) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = -cos(5*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3*pi/2) (0),
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


lemma Trigo_554_test : 2*sin(5*pi/12)*sin(1513*pi/12)=1 / 2:=
begin
have : cos(5*pi/12) = sin(1513*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (63),
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


lemma Trigo_555_test (h0 : tan(551*pi/6)≠ 0) : 1/tan(551*pi/6)=- sqrt( 3 ):=
begin
have : -((-1) / tan(551 * pi / 6)) = 1/tan(551*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(175*pi/3) = -1 / tan(551*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (175*pi/3) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(175*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (59),
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


lemma Trigo_556_test : -sin(189*pi)=0:=
begin
have : sin(8*pi) = sin(189*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(8*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (3),
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


lemma Trigo_557_test (h0 : cos((1019*pi/6)/2)≠ 0) (h1 : sin(1019*pi/6)≠ 0) : -(1 - cos(1019*pi/6))/sin(1019*pi/6)=2 - sqrt( 3 ):=
begin
have : -((1 - cos(1019 * pi / 6)) / sin(1019 * pi / 6)) = -(1 - cos(1019*pi/6))/sin(1019*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1019*pi/12) = ( 1 - cos(1019*pi/6) ) / sin(1019*pi/6),
{
have : tan(1019*pi/12) = tan((1019*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(1019*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (85),
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


lemma Trigo_558_test : sin(-5*pi/2)*cos(2*pi) - sin(-2*pi) + sin(2*pi)*cos(-5*pi/2)=-2*sin(3*pi/4)*sin(235*pi/4):=
begin
have : sin((-5) * pi / 2) * cos(2 * pi) + sin(2 * pi) * cos((-5) * pi / 2) - sin((-2) * pi) = sin(-5*pi/2)*cos(2*pi) - sin(-2*pi) + sin(2*pi)*cos(-5*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(-5*pi/2) * cos(2*pi) + sin(2*pi) * cos(-5*pi/2),
{
have : sin(-pi/2) = sin((-5*pi/2) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(3 * pi / 4) * -sin(235 * pi / 4) = -2*sin(3*pi/4)*sin(235*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-5*pi/4) = -sin(235*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-5*pi/4) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) - sin(-2*pi) = 2 * sin(3*pi/4) * cos(-5*pi/4),
{
rw sin_sub_sin,
have : cos(((-pi/2) + (-2*pi))/2) = cos(-5*pi/4),
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
},
rw this,
end


lemma Trigo_559_test : -1 + 2*(1 - 2*sin(pi/24)**2)**2=sqrt( 3 ) / 2:=
begin
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


lemma Trigo_560_test : sin(133*pi/2)=-3*sin(129*pi/2) + 4*sin(129*pi/2)**3:=
begin
have : 4 * sin(129 * pi / 2) ** 3 - 3 * sin(129 * pi / 2) = -3*sin(129*pi/2) + 4*sin(129*pi/2)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = sin(129*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(6*pi) = sin(133*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (6*pi) (36),
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


lemma Trigo_561_test (h0 : cos(pi/3)≠ 0) : -cos(-pi/2)*cos(350*pi/3) + sin(-pi/2)*cos(5*pi/6)=sin(2*pi/3) / ( 2 * cos(pi/3) ):=
begin
have : -cos(350 * pi / 3) * cos(-pi / 2) + sin(-pi / 2) * cos(5 * pi / 6) = -cos(-pi/2)*cos(350*pi/3) + sin(-pi/2)*cos(5*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = -cos(350*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(5*pi/6) * cos(-pi/2) + sin(-pi/2) * cos(5*pi/6),
{
have : sin(pi/3) = sin((5*pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_562_test : -sin(pi/24)**2 + cos(2231*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -sin(pi / 24) ** 2 + (-cos(2231 * pi / 24)) ** 2 = -sin(pi/24)**2 + cos(2231*pi/24)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -cos(2231*pi/24),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/24) (46),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_563_test : -sin(243*pi/2)*cos(1133*pi/6)=sin(-2*pi/3) / 2 + sin(4*pi/3) / 2:=
begin
have : -cos(1133 * pi / 6) * sin(243 * pi / 2) = -sin(243*pi/2)*cos(1133*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(1133*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(243*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(pi) = sin(-2*pi/3) / 2 + sin(4*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (pi)) = sin(4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (pi)) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_564_test (h0 : cos(-pi/2)≠ 0) : sin(339*pi/2)/cos(-pi/2)=1 / tan(97*pi):=
begin
have : sin(-pi/2) = sin(339*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/2) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = sin(-pi/2) / cos(-pi/2),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = 1 / tan(97*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/2) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_565_test : -sin(pi/6)*sin(797*pi/6)=-cos(0)/2 - sin(pi/6)**2/2 + cos(pi/6)**2/2:=
begin
have : (-sin(pi / 6) ** 2 + cos(pi / 6) ** 2) / 2 - cos(0) / 2 = -cos(0)/2 - sin(pi/6)**2/2 + cos(pi/6)**2/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi / 6) * -sin(797 * pi / 6) = -sin(pi/6)*sin(797*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(797*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/6) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * sin(-pi/6) = cos(pi/3) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_566_test : -1 + 2*cos(pi/12)**2=-cos(101*pi/6):=
begin
have : sin(542*pi/3) = -cos(101*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (542*pi/3) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : cos(pi/6) = sin(542*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/6) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_567_test (h0 : tan(91*pi/3)≠ 0) (h1 : cos((182*pi/3)/2)≠ 0) (h2 : (1-cos(182*pi/3))≠ 0) (h3 : ((1-cos(182*pi/3))/sin(182*pi/3))≠ 0) (h4 : sin(182*pi/3)≠ 0) : -sin(182*pi/3)/(1 - cos(182*pi/3))=- 1 / tan(28*pi/3):=
begin
have : (-1) / ((1 - cos(182 * pi / 3)) / sin(182 * pi / 3)) = -sin(182*pi/3)/(1 - cos(182*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(91*pi/3) = ( 1 - cos(182*pi/3) ) / sin(182*pi/3),
{
have : tan(91*pi/3) = tan((182*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(91 * pi / 3) = -1/tan(91*pi/3),
{
field_simp at *,
},
have : tan(-pi/6) = -1 / tan(91*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = - 1 / tan(28*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_568_test (h0 : cos((395*pi/6)/2)≠ 0) (h1 : (1+cos(395*pi/6))≠ 0) (h2 : (cos(395*pi/6)+1)≠ 0) : -sin(395*pi/6)/(cos(395*pi/6) + 1)=2 - sqrt( 3 ):=
begin
have : -(sin(395 * pi / 6) / (1 + cos(395 * pi / 6))) = -sin(395*pi/6)/(cos(395*pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(395*pi/12) = sin(395*pi/6) / ( 1 + cos(395*pi/6) ),
{
have : tan(395*pi/12) = tan((395*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(395*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (33),
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




lemma Trigo_570_test : cos(17*pi/3)=sin(-2*pi)*cos(pi/6) + (-sin(-pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi))*cos(-2*pi):=
begin
have : sin((-2) * pi) * cos(pi / 6) + (sin((-5) * pi / 6) * cos(-pi) - sin(-pi) * cos((-5) * pi / 6)) * cos((-2) * pi) = sin(-2*pi)*cos(pi/6) + (-sin(-pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(-pi))*cos(-2*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-11*pi/6) = cos(17*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-11*pi/6) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-11*pi/6) = sin(-2*pi) * cos(pi/6) + sin(pi/6) * cos(-2*pi),
{
have : sin(-11*pi/6) = sin((-2*pi) + (pi/6)),
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


lemma Trigo_571_test : -sin(pi/3)**2 + cos(365*pi/3)**2=- 1 / 2:=
begin
have : cos(pi/3) = cos(365*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (61),
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


lemma Trigo_572_test : sin(322*pi/3)**2=1 - sin(-pi/6) ** 2:=
begin
have : (-sin(322 * pi / 3)) ** 2 = sin(322*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(563*pi/6) = -sin(322*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (563*pi/6) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(563*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) ** 2 = 1 - sin(-pi/6) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_573_test : cos(pi) - cos(847*pi/12)**2 + sin(847*pi/12)**2=2 * cos(5*pi/12) * cos(7*pi/12):=
begin
have : cos(pi) - (-sin(847 * pi / 12) ** 2 + cos(847 * pi / 12) ** 2) = cos(pi) - cos(847*pi/12)**2 + sin(847*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(847*pi/6) = -sin(847*pi/12) ** 2 + cos(847*pi/12) ** 2,
{
have : cos(847*pi/6) = cos(2*(847*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) + -cos(847 * pi / 6) = cos(pi) - cos(847*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(847*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) + cos(pi/6) = 2 * cos(5*pi/12) * cos(7*pi/12),
{
rw cos_add_cos,
have : cos(((pi) + (pi/6))/2) = cos(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi) - (pi/6))/2) = cos(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_574_test : cos(377*pi/6)=-sin(pi/2)*sin(356*pi/3) + cos(pi/3)*cos(pi/2):=
begin
have : cos(5*pi/6) = cos(377*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (5*pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 2) * sin(356 * pi / 3) + cos(pi / 2) * cos(pi / 3) = -sin(pi/2)*sin(356*pi/3) + cos(pi/3)*cos(pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = sin(356*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/6) = - sin(pi/2) * sin(pi/3) + cos(pi/2) * cos(pi/3),
{
have : cos(5*pi/6) = cos((pi/2) + (pi/3)),
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




lemma Trigo_576_test : -4*cos(1955*pi/36)**3 + 3*cos(1955*pi/36)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(4 * cos(1955 * pi / 36) ** 3 - 3 * cos(1955 * pi / 36)) = -4*cos(1955*pi/36)**3 + 3*cos(1955*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1955*pi/12) = 4 * cos(1955*pi/36) ** 3 - 3 * cos(1955*pi/36),
{
have : cos(1955*pi/12) = cos(3*(1955*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
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


lemma Trigo_577_test (h0 : cos((82*pi/3)/2)≠ 0) (h1 : (1+cos(82*pi/3))≠ 0) (h2 : (cos(82*pi/3)+1)≠ 0) : sin(82*pi/3)/(cos(82*pi/3) + 1)=- sqrt( 3 ):=
begin
have : sin(82 * pi / 3) / (1 + cos(82 * pi / 3)) = sin(82*pi/3)/(cos(82*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(41*pi/3) = sin(82*pi/3) / ( 1 + cos(82*pi/3) ),
{
have : tan(41*pi/3) = tan((82*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = tan(41*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (2*pi/3) (13),
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


lemma Trigo_578_test (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : cos(67*pi/2)/(2*cos(pi))=- cos(77*pi/2):=
begin
have : sin(2*pi) = cos(67*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (15),
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
have : sin(pi) = - cos(77*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_579_test : sin(835*pi/6)**2=1 - (sin(5*pi/3)*cos(-2*pi) + sin(-2*pi)*cos(5*pi/3))**2:=
begin
have : (-sin(835 * pi / 6)) ** 2 = sin(835*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(835*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (sin(5 * pi / 3) * cos((-2) * pi) + sin((-2) * pi) * cos(5 * pi / 3)) ** 2 = 1 - (sin(5*pi/3)*cos(-2*pi) + sin(-2*pi)*cos(5*pi/3))**2,
{
field_simp at *,
},
have : sin(-pi/3) = sin(5*pi/3) * cos(-2*pi) + sin(-2*pi) * cos(5*pi/3),
{
have : sin(-pi/3) = sin((5*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) ** 2 = 1 - sin(-pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_580_test : 2*(sin(13*pi/24)*cos(-pi/2) + sin(-pi/2)*cos(13*pi/24))*cos(pi/24)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi/24) = sin(13*pi/24) * cos(-pi/2) + sin(-pi/2) * cos(13*pi/24),
{
have : sin(pi/24) = sin((13*pi/24) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = 2 * sin(pi/24) * cos(pi/24),
{
have : sin(pi/12) = sin(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = - sqrt( 2 ) / 4 + sqrt( 6 ) / 4,
{
rw sin_pi_div_twelve,
},
rw this,
end


lemma Trigo_581_test : 2*sin(339*pi/8)*cos(339*pi/8)=sqrt( 2 ) / 2:=
begin
have : sin(339*pi/4) = 2 * sin(339*pi/8) * cos(339*pi/8),
{
have : sin(339*pi/4) = sin(2*(339*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(339*pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/4) (42),
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


lemma Trigo_582_test (h0 : tan(581*pi/6)≠ 0) (h1 : tan(460*pi/3)≠ 0) (h2 : ((-1)/tan(460*pi/3))≠ 0) : tan(460*pi/3)=- 1 / tan(155*pi/6):=
begin
have : (-1) / ((-1) / tan(460 * pi / 3)) = tan(460*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(581*pi/6) = -1 / tan(460*pi/3),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (581*pi/6) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(581 * pi / 6) = -1/tan(581*pi/6),
{
field_simp at *,
},
have : tan(pi/3) = -1 / tan(581*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = - 1 / tan(155*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_583_test : cos(1375*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(1015*pi/6) = cos(1375*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (1015*pi/6) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = cos(1015*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/6) (85),
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


lemma Trigo_584_test : cos(-158*pi)=1:=
begin
have : - -cos((-158) * pi) = cos(-158*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(359*pi/2) = -cos(-158*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (359*pi/2) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(359*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (89),
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


lemma Trigo_585_test (h0 : cos(pi/12)≠ 0) (h1 : (2*cos(pi/12))≠ 0) (h2 : (2*(2*cos(pi/24)**2-1))≠ 0) (h3 : (2*(-1+2*cos(pi/24)**2))≠ 0) : sin(pi/6)/(2*(-1 + 2*cos(pi/24)**2))=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(pi / 6) / (2 * (2 * cos(pi / 24) ** 2 - 1)) = sin(pi/6)/(2*(-1 + 2*cos(pi/24)**2)),
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


lemma Trigo_586_test (h0 : cos(43*pi/8)≠ 0) (h1 : (1-tan(43*pi/8)**2)≠ 0) : -2*tan(43*pi/8)/(1 - tan(43*pi/8)**2)=1:=
begin
have : -(2 * tan(43 * pi / 8) / (1 - tan(43 * pi / 8) ** 2)) = -2*tan(43*pi/8)/(1 - tan(43*pi/8)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(43*pi/4) = 2 * tan(43*pi/8) / ( 1 - tan(43*pi/8) ** 2 ),
{
have : tan(43*pi/4) = tan(2*(43*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = -tan(43*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (11),
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


lemma Trigo_587_test (h0 : sin(527*pi/3)≠ 0) (h1 : (2*sin(527*pi/3))≠ 0) : sin(1054*pi/3)/(2*sin(527*pi/3))=1 / 2:=
begin
have : cos(527*pi/3) = sin(1054*pi/3) / ( 2 * sin(527*pi/3) ),
{
have : sin(1054*pi/3) = sin(2*(527*pi/3)),
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
have : cos(pi/3) = cos(527*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (88),
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


lemma Trigo_588_test : 1 - 2*sin(pi/4)**2=cos(-147*pi/2):=
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
have : cos((-147) * pi / 2) = cos(-147*pi/2),
{
field_simp at *,
},
have : sin(176*pi) = cos(-147*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (176*pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = sin(176*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_589_test : -sin(pi/6)*cos(815*pi/6) - sin(815*pi/6)*cos(pi/6)=4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6):=
begin
have : -(sin(815 * pi / 6) * cos(pi / 6) + sin(pi / 6) * cos(815 * pi / 6)) = -sin(pi/6)*cos(815*pi/6) - sin(815*pi/6)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(136*pi) = sin(815*pi/6) * cos(pi/6) + sin(pi/6) * cos(815*pi/6),
{
have : sin(136*pi) = sin((815*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(136*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (67),
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


lemma Trigo_590_test (h0 : cos(-pi/6)≠ 0) (h1 : (1-tan(-pi/6)**2)≠ 0) (h2 : cos(-pi/12)≠ 0) (h3 : (1-tan(-pi/12)**2)≠ 0) (h4 : ((1-tan(-pi/12)**2)*(-4*tan(-pi/12)**2/(1-tan(-pi/12)**2)**2+1))≠ 0) (h5 : (1-(2*tan(-pi/12)/(1-tan(-pi/12)**2))**2)≠ 0) : 4*tan(-pi/12)/((1 - tan(-pi/12)**2)*(-4*tan(-pi/12)**2/(1 - tan(-pi/12)**2)**2 + 1))=- tan(265*pi/3):=
begin
have : 2 * (2 * tan(-pi / 12) / (1 - tan(-pi / 12) ** 2)) / (1 - (2 * tan(-pi / 12) / (1 - tan(-pi / 12) ** 2)) ** 2) = 4*tan(-pi/12)/((1 - tan(-pi/12)**2)*(-4*tan(-pi/12)**2/(1 - tan(-pi/12)**2)**2 + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : tan(-pi/3) = 2 * tan(-pi/6) / ( 1 - tan(-pi/6) ** 2 ),
{
have : tan(-pi/3) = tan(2*(-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - tan(265*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_591_test (h0 : sin(110*pi)≠ 0) (h1 : (2*sin(110*pi))≠ 0) : sin(220*pi)/(2*sin(110*pi))=1:=
begin
have : cos(110*pi) = sin(220*pi) / ( 2 * sin(110*pi) ),
{
have : sin(220*pi) = sin(2*(110*pi)),
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
have : sin(pi/2) = cos(110*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (54),
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


lemma Trigo_592_test (h0 : sin(175*pi/6)≠ 0) (h1 : -sin(175*pi/6)≠ 0) (h2 : cos(pi/2)≠ 0) (h3 : cos(pi/6)≠ 0) (h4 : (1+tan(pi/2)*tan(pi/6))≠ 0) (h5 : (1+tan(pi/6)*tan(pi/2))≠ 0) : -sin(pi/3)/sin(175*pi/6)=(-tan(pi/6) + tan(pi/2))/(1 + tan(pi/6)*tan(pi/2)):=
begin
have : (tan(pi / 2) - tan(pi / 6)) / (1 + tan(pi / 2) * tan(pi / 6)) = (-tan(pi/6) + tan(pi/2))/(1 + tan(pi/6)*tan(pi/2)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = ( tan(pi/2) - tan(pi/6) ) / ( 1 + tan(pi/2) * tan(pi/6) ),
{
have : tan(pi/3) = tan((pi/2) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(pi / 3) / -sin(175 * pi / 6) = -sin(pi/3)/sin(175*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(175*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_593_test (h0 : tan(109*pi/2)≠ 0) : -1/tan(109*pi/2)=- tan(19*pi):=
begin
have : -(1 / tan(109 * pi / 2)) = -1/tan(109*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(38*pi) = 1 / tan(109*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (38*pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = -tan(38*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = - tan(19*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_594_test : sin(pi/2) * sin(-pi/6)=-2*sin(1807*pi/18)**3 + cos(2*pi/3)/2 + 3*sin(1807*pi/18)/2:=
begin
have : (-2) * sin(1807 * pi / 18) ** 3 + cos(2 * pi / 3) / 2 + 3 * sin(1807 * pi / 18) / 2 = -2*sin(1807*pi/18)**3 + cos(2*pi/3)/2 + 3*sin(1807*pi/18)/2,
{
field_simp at *,
},
have : cos(pi/9) = sin(1807*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2 * pi / 3) / 2 - (4 * cos(pi / 9) ** 3 - 3 * cos(pi / 9)) / 2 = -2*cos(pi/9)**3 + cos(2*pi/3)/2 + 3*cos(pi/9)/2,
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
have : sin(pi/2) * sin(-pi/6) = cos(2*pi/3) / 2 - cos(pi/3) / 2,
{
rw sin_mul_sin,
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


lemma Trigo_595_test (h0 : cos(5*pi/12)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(5*pi/12)*tan(-pi/3))≠ 0) (h3 : (tan(-pi/3)*tan(5*pi/12)+1)≠ 0) (h4 : cos(-pi/3)≠ 0) (h5 : cos(5*pi/12)≠ 0) (h6 : 1 + tan(-pi/3) * tan(5*pi/12)≠ 0) : -tan(-3*pi/4)=- 1:=
begin
have : (-1) * ((tan(-pi / 3) * tan(5 * pi / 12) + 1) * tan((-3) * pi / 4)) / (tan(-pi / 3) * tan(5 * pi / 12) + 1) = -tan(-3*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) - tan(5*pi/12) = ( tan(-pi/3) * tan(5*pi/12) + 1 ) * tan(-3*pi/4),
{
rw tan_sub_tan,
have : tan((-pi/3) - (5*pi/12)) = tan(-3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -1*(tan(-pi/3) - tan(5*pi/12)) = (-tan(-pi/3)+tan(5*pi/12)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan(5 * pi / 12) - tan(-pi / 3)) / (1 + tan(5 * pi / 12) * tan(-pi / 3)) = (-tan(-pi/3) + tan(5*pi/12))/(tan(-pi/3)*tan(5*pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = ( tan(5*pi/12) - tan(-pi/3) ) / ( 1 + tan(5*pi/12) * tan(-pi/3) ),
{
have : tan(3*pi/4) = tan((5*pi/12) - (-pi/3)),
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


lemma Trigo_596_test (h0 : cos((4*pi/3)/2)≠ 0) (h1 : (1+cos(4*pi/3))≠ 0) (h2 : (cos(4*pi/3)+1)≠ 0) (h3 : (1-cos(389*pi/3))≠ 0) (h4 : (-cos(389*pi/3)+1)≠ 0) : sin(4*pi/3)/(1 - cos(389*pi/3))=- sqrt( 3 ):=
begin
have : sin(4 * pi / 3) / (-cos(389 * pi / 3) + 1) = sin(4*pi/3)/(1 - cos(389*pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/3) = -cos(389*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (4*pi/3) (65),
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


lemma Trigo_597_test : -sin(445*pi/3)=2*(-sin(-pi/6)**2 + cos(-pi/6)**2)*sin(-pi/3):=
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
have : sin(-2*pi/3) = -sin(445*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_598_test : sin(71*pi/6)=-1 + 2*sin(833*pi/6)**2:=
begin
have : 2 * sin(833 * pi / 6) ** 2 - 1 = -1 + 2*sin(833*pi/6)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(833*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi/3) = sin(71*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (6),
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


lemma Trigo_599_test : 4*cos(1823*pi/18)**3 - 3*cos(1823*pi/18)=sqrt( 3 ) / 2:=
begin
have : (-4) * (-cos(1823 * pi / 18)) ** 3 + 3 * -cos(1823 * pi / 18) = 4*cos(1823*pi/18)**3 - 3*cos(1823*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = -cos(1823*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/9) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(2 * pi / 9) ** 3 + 3 * sin(2 * pi / 9) = -4*sin(2*pi/9)**3 + 3*sin(2*pi/9),
{
field_simp at *,
},
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
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sqrt( 3 ) / 2,
{
rw sin_two_pi_div_three,
},
rw this,
end


lemma Trigo_600_test : -3*sin(15*pi) + 4*sin(15*pi)**3=sin(189*pi):=
begin
have : -((-4) * sin(15 * pi) ** 3 + 3 * sin(15 * pi)) = -3*sin(15*pi) + 4*sin(15*pi)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(45*pi) = -4 * sin(15*pi) ** 3 + 3 * sin(15*pi),
{
have : sin(45*pi) = sin(3*(15*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(45*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(189*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_601_test (h0 : cos((2*pi)/2)≠ 0) (h1 : (1+cos(2*pi))≠ 0) (h2 : tan(70*pi)≠ 0) (h3 : ((-1)/tan(70*pi))≠ 0) : sin(2*pi)/(1 + cos(2*pi))=tan(70*pi):=
begin
have : (-1) / ((-1) / tan(70 * pi)) = tan(70*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(25*pi/2) = -1 / tan(70*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (25*pi/2) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : tan(pi) = - 1 / tan(25*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_602_test : cos(-pi/3)*cos(4*pi/3) + sin(-pi/3)*sin(4*pi/3)=-cos(-7*pi/3)/2 + cos(5*pi/3)/2 + cos(-2*pi)*cos(-pi/3):=
begin
have : sin(4 * pi / 3) * sin(-pi / 3) + cos(4 * pi / 3) * cos(-pi / 3) = cos(-pi/3)*cos(4*pi/3) + sin(-pi/3)*sin(4*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/3) = sin(4*pi/3) * sin(-pi/3) + cos(4*pi/3) * cos(-pi/3),
{
have : cos(5*pi/3) = cos((4*pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5 * pi / 3) / 2 - cos((-7) * pi / 3) / 2 + cos(-pi / 3) * cos((-2) * pi) = -cos(-7*pi/3)/2 + cos(5*pi/3)/2 + cos(-2*pi)*cos(-pi/3),
{
field_simp at *,
ring,
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
conv {to_rhs, rw ← this,},
have : (sin(-pi/3) * sin(-2*pi)) = sin(-pi/3)*sin(-2*pi),
{
ring,
},
have : cos(5*pi/3) = sin(-pi/3) * sin(-2*pi) + cos(-pi/3) * cos(-2*pi),
{
have : cos(5*pi/3) = cos((-pi/3) - (-2*pi)),
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


lemma Trigo_603_test (h0 : cos(pi)≠ 0) (h1 : (1-2*sin(pi/2)**2)≠ 0) : sin(52*pi)/(1 - 2*sin(pi/2)**2)=tan(pi):=
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
have : sin(pi) = sin(52*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) / cos(pi) = tan(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_604_test : (sin(-pi/2)*sin(pi/6) + cos(-pi/2)*cos(pi/6))*cos(-pi/6) - sin(-pi/6)*sin(2*pi/3)=0:=
begin
have : cos(-pi / 6) * (sin(pi / 6) * sin(-pi / 2) + cos(pi / 6) * cos(-pi / 2)) - sin(-pi / 6) * sin(2 * pi / 3) = (sin(-pi/2)*sin(pi/6) + cos(-pi/2)*cos(pi/6))*cos(-pi/6) - sin(-pi/6)*sin(2*pi/3),
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
have : -sin(2 * pi / 3) * sin(-pi / 6) + cos(2 * pi / 3) * cos(-pi / 6) = cos(-pi/6)*cos(2*pi/3) - sin(-pi/6)*sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(2*pi/3) * sin(-pi/6) + cos(2*pi/3) * cos(-pi/6),
{
have : cos(pi/2) = cos((2*pi/3) + (-pi/6)),
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


lemma Trigo_605_test : 4*sin(1495*pi/18)**3 - 3*sin(1495*pi/18)=- sin(55*pi/6):=
begin
have : (-4) * (-sin(1495 * pi / 18)) ** 3 + 3 * -sin(1495 * pi / 18) = 4*sin(1495*pi/18)**3 - 3*sin(1495*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = -sin(1495*pi/18),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/18) (41),
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
have : sin(pi/6) = - sin(55*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_606_test : -sin(-pi/6)*sin(1213*pi/12) - cos(-pi/6)*cos(1213*pi/12)=sqrt( 2 ) / 2:=
begin
have : -(sin(1213 * pi / 12) * sin(-pi / 6) + cos(1213 * pi / 12) * cos(-pi / 6)) = -sin(-pi/6)*sin(1213*pi/12) - cos(-pi/6)*cos(1213*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(405*pi/4) = sin(1213*pi/12) * sin(-pi/6) + cos(1213*pi/12) * cos(-pi/6),
{
have : cos(405*pi/4) = cos((1213*pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = -cos(405*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/4) (50),
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


lemma Trigo_607_test : -3*cos(7*pi/3) + 4*cos(7*pi/3)**3=cos(141*pi):=
begin
have : (-3) * cos(7 * pi / 3) + 4 * cos(7 * pi / 3) ** 3 = -3*cos(7*pi/3) + 4*cos(7*pi/3)**3,
{
field_simp at *,
},
have : cos(-pi/3) = cos(7*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (1),
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
have : cos(-pi) = cos(141*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_608_test : -sin(pi/12)**2 + (-3*cos(pi/36) + 4*cos(pi/36)**3)**2=sqrt( 3 ) / 2:=
begin
have : -sin(pi / 12) ** 2 + (4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36)) ** 2 = -sin(pi/12)**2 + (-3*cos(pi/36) + 4*cos(pi/36)**3)**2,
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


lemma Trigo_609_test (h0 : cos(-pi/3)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (2*cos(-pi/3))≠ 0) : -cos(345*pi/2) + cos(-pi/6)=-sin(-2*pi/3)*sin(pi/6)/cos(-pi/3):=
begin
have : (-2) * (sin((-2) * pi / 3) / (2 * cos(-pi / 3))) * sin(pi / 6) = -sin(-2*pi/3)*sin(pi/6)/cos(-pi/3),
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
have : cos(-pi / 6) - cos(345 * pi / 2) = -cos(345*pi/2) + cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(345*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) - cos(pi/2) = - 2 * sin(-pi/3) * sin(pi/6),
{
rw cos_sub_cos,
have : sin(((-pi/6) + (pi/2))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (pi/2))/2) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end




lemma Trigo_611_test (h0 : tan(65*pi/6)≠ 0) (h1 : cos(65*pi/12)≠ 0) (h2 : (2*tan(65*pi/12)/(1-tan(65*pi/12)**2))≠ 0) (h3 : (1-tan(65*pi/12)**2)≠ 0) (h4 : (2*tan(65*pi/12))≠ 0) : (1 - tan(65*pi/12)**2)/(2*tan(65*pi/12))=1 / tan(173*pi/6):=
begin
have : 1 / (2 * tan(65 * pi / 12) / (1 - tan(65 * pi / 12) ** 2)) = (1 - tan(65*pi/12)**2)/(2*tan(65*pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(65*pi/6) = 2 * tan(65*pi/12) / ( 1 - tan(65*pi/12) ** 2 ),
{
have : tan(65*pi/6) = tan(2*(65*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = 1 / tan(65*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = 1 / tan(173*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/3) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_612_test : sin(-pi/4)*cos(-pi/2) - cos(-pi/4)*cos(151*pi)=sqrt( 2 ) / 2:=
begin
have : sin(-pi / 4) * cos(-pi / 2) - cos(151 * pi) * cos(-pi / 4) = sin(-pi/4)*cos(-pi/2) - cos(-pi/4)*cos(151*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(151*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(-pi/4) * cos(-pi/2) - sin(-pi/2) * cos(-pi/4),
{
have : sin(pi/4) = sin((-pi/4) - (-pi/2)),
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


lemma Trigo_613_test : cos(475*pi/6)=- sqrt( 3 ) / 2:=
begin
have : cos(319*pi/6) = cos(475*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (319*pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = cos(319*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/6) (27),
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


lemma Trigo_614_test : cos(pi)=-1 + 2*sin(121*pi)**2:=
begin
have : 1 - 2 * (1 - sin(121 * pi) ** 2) = -1 + 2*sin(121*pi)**2,
{
ring,
},
conv {to_rhs, rw ← this,},
have : cos(121*pi) ** 2 = 1 - sin(121*pi) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : 1 - 2 * (-cos(121 * pi)) ** 2 = 1 - 2*cos(121*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = -cos(121*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (60),
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


lemma Trigo_615_test : cos(pi/2)*cos(2*pi/3) + sin(pi/2)*sin(223*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(2*pi/3) = sin(223*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi / 3) * sin(pi / 2) + cos(2 * pi / 3) * cos(pi / 2) = cos(pi/2)*cos(2*pi/3) + sin(pi/2)*sin(2*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(2*pi/3) * sin(pi/2) + cos(2*pi/3) * cos(pi/2),
{
have : cos(pi/6) = cos((2*pi/3) - (pi/2)),
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


lemma Trigo_616_test : -4*sin(pi/9)**3 + 3*sin(pi/9)=sin(632*pi/3):=
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
have : - -sin(632 * pi / 3) = sin(632*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(967*pi/6) = -sin(632*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (967*pi/6) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = - cos(967*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_617_test : cos(613*pi/3)=- cos(238*pi/3):=
begin
have : sin(77*pi/6) = cos(613*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (77*pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(77*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = - cos(238*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_619_test : -sin(pi/2)**2 + cos(131*pi/2)**2=- 1:=
begin
have : cos(pi/2) = cos(131*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (33),
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
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_620_test : sin(pi)*sin(5*pi/4) + (cos(-pi)*cos(2*pi) - sin(-pi)*sin(2*pi))*cos(5*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(pi) * sin(5 * pi / 4) + (-sin(-pi) * sin(2 * pi) + cos(-pi) * cos(2 * pi)) * cos(5 * pi / 4) = sin(pi)*sin(5*pi/4) + (cos(-pi)*cos(2*pi) - sin(-pi)*sin(2*pi))*cos(5*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(-pi) * sin(2*pi) + cos(-pi) * cos(2*pi),
{
have : cos(pi) = cos((-pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
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


lemma Trigo_621_test : -cos(36*pi)=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : sin(137*pi/2) = cos(36*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (137*pi/2) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = -sin(137*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi) (35),
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


lemma Trigo_622_test : -cos(232*pi)=- 1:=
begin
have : sin(249*pi/2) = cos(232*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (249*pi/2) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(249*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (61),
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


lemma Trigo_623_test : -1 + 2*sin(59*pi)**2=- 1:=
begin
have : -(1 - 2 * sin(59 * pi) ** 2) = -1 + 2*sin(59*pi)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(118*pi) = 1 - 2 * sin(59*pi) ** 2,
{
have : cos(118*pi) = cos(2*(59*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(118*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (58),
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




lemma Trigo_625_test : (-1 + 2*cos(-pi/4)**2)**2=cos(-pi) / 2 + 1 / 2:=
begin
have : (-(1 - cos(-pi / 4) ** 2) + cos(-pi / 4) ** 2) ** 2 = (-1 + 2*cos(-pi/4)**2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) ** 2 = 1 - cos(-pi/4) ** 2,
{
rw sin_sq,
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


lemma Trigo_626_test : (-1 + 2*sin(735*pi/4)**2)*cos(pi)=cos(-3*pi/2) / 2 + cos(pi/2) / 2:=
begin
have : (-1 + 2 * (-sin(735 * pi / 4)) ** 2) * cos(pi) = (-1 + 2*sin(735*pi/4)**2)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/4) = -sin(735*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * cos(-pi / 4) ** 2 - 1) * cos(pi) = (-1 + 2*cos(-pi/4)**2)*cos(pi),
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
have : cos(-pi/2) * cos(pi) = cos(-3*pi/2) / 2 + cos(pi/2) / 2,
{
rw cos_mul_cos,
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


lemma Trigo_627_test : 1 - 2*sin(167*pi/3)**2=- 1 / 2:=
begin
have : cos(334*pi/3) = 1 - 2 * sin(167*pi/3) ** 2,
{
have : cos(334*pi/3) = cos(2*(167*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = cos(334*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/3) (56),
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


lemma Trigo_628_test : -4*sin(361*pi/36)**3 + 3*sin(361*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-4) * sin(361 * pi / 36) ** 3 + 3 * sin(361 * pi / 36) = -4*sin(361*pi/36)**3 + 3*sin(361*pi/36),
{
field_simp at *,
},
have : sin(pi/36) = sin(361*pi/36),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/36) (5),
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


lemma Trigo_629_test : sin(-2*pi)*cos(-503*pi/6)=sin(-13*pi/6) / 2 + sin(-11*pi/6) / 2:=
begin
have : sin((-2) * pi) * cos((-503) * pi / 6) = sin(-2*pi)*cos(-503*pi/6),
{
field_simp at *,
},
have : sin(469*pi/3) = cos(-503*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (469*pi/3) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi) * sin(469 * pi / 3) = sin(-2*pi)*sin(469*pi/3),
{
field_simp at *,
},
have : cos(pi/6) = sin(469*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(pi/6) = sin(-13*pi/6) / 2 + sin(-11*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (pi/6)) = sin(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (pi/6)) = sin(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end




lemma Trigo_631_test : sin(1685*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : - -sin(1685 * pi / 12) = sin(1685*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1547*pi/12) = -sin(1685*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (1547*pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(1547*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (64),
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


lemma Trigo_632_test (h0 : cos((599*pi/6)/2)≠ 0) (h1 : (cos(599*pi/6)+1)≠ 0) (h2 : (1+cos(599*pi/6))≠ 0) : -sin(599*pi/6)/(cos(599*pi/6) + 1)=2 - sqrt( 3 ):=
begin
have : -(sin(599 * pi / 6) / (1 + cos(599 * pi / 6))) = -sin(599*pi/6)/(cos(599*pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(599*pi/12) = sin(599*pi/6) / ( 1 + cos(599*pi/6) ),
{
have : tan(599*pi/12) = tan((599*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(599*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (50),
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


lemma Trigo_633_test (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) : -cos(11*pi/6)=cos(pi/6)*cos(pi) - sin(pi/6)*sin(2*pi)/(2*cos(pi)):=
begin
have : -sin(pi / 6) * (sin(2 * pi) / (2 * cos(pi))) + cos(pi / 6) * cos(pi) = cos(pi/6)*cos(pi) - sin(pi/6)*sin(2*pi)/(2*cos(pi)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : cos(7*pi/6) = -cos(11*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (7*pi/6) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/6) = - sin(pi/6) * sin(pi) + cos(pi/6) * cos(pi),
{
have : cos(7*pi/6) = cos((pi/6) + (pi)),
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


lemma Trigo_634_test (h0 : cos(-pi/6)≠ 0) (h1 : (2*cos(-pi/6))≠ 0) : cos(0)=-(sin(2*pi/3)*cos(-pi) + sin(-pi)*cos(2*pi/3))*sin(pi/6)/(2*cos(-pi/6)) + cos(-pi/6)*cos(pi/6):=
begin
have : sin(-pi/3) = sin(2*pi/3) * cos(-pi) + sin(-pi) * cos(2*pi/3),
{
have : sin(-pi/3) = sin((2*pi/3) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : -(sin(-pi / 3) / (2 * cos(-pi / 6))) * sin(pi / 6) + cos(-pi / 6) * cos(pi / 6) = -sin(-pi/3)*sin(pi/6)/(2*cos(-pi/6)) + cos(-pi/6)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_635_test : -sin(29*pi)=-4*cos(203*pi/6)**3 + 3*cos(203*pi/6):=
begin
have : -(4 * cos(203 * pi / 6) ** 3 - 3 * cos(203 * pi / 6)) = -4*cos(203*pi/6)**3 + 3*cos(203*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(203*pi/2) = 4 * cos(203*pi/6) ** 3 - 3 * cos(203*pi/6),
{
have : cos(203*pi/2) = cos(3*(203*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = -sin(29*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - cos(203*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_636_test (h0 : cos(-pi)≠ 0) (h1 : (2*cos(-pi))≠ 0) (h2 : (4*cos(-pi)**2)≠ 0) : sin(-2*pi)**2/(4*cos(-pi)**2)=cos(51*pi)/2 + 1/2:=
begin
have : (sin((-2) * pi) / (2 * cos(-pi))) ** 2 = sin(-2*pi)**2/(4*cos(-pi)**2),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : 1 / 2 - -cos(51 * pi) / 2 = cos(51*pi)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = -cos(51*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_637_test : -sin(75*pi)=-sin(85*pi):=
begin
have : cos(29*pi/2) = -sin(85*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (29*pi/2) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -sin(75*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = cos(29*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_638_test : sin(-pi/6)*sin(pi/3) + (cos(-2*pi/3)*cos(pi/2) - sin(-2*pi/3)*sin(pi/2))*cos(pi/3)=4 * cos(pi/6) ** 3 - 3 * cos(pi/6):=
begin
have : sin(-pi / 6) * sin(pi / 3) + (-sin((-2) * pi / 3) * sin(pi / 2) + cos((-2) * pi / 3) * cos(pi / 2)) * cos(pi / 3) = sin(-pi/6)*sin(pi/3) + (cos(-2*pi/3)*cos(pi/2) - sin(-2*pi/3)*sin(pi/2))*cos(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(-2*pi/3) * sin(pi/2) + cos(-2*pi/3) * cos(pi/2),
{
have : cos(-pi/6) = cos((-2*pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_639_test : -sin(577*pi/6)*cos(1081*pi/6)=sin(-pi/3) / 2 + sin(0) / 2:=
begin
have : cos(pi/6) = cos(1081*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(577*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (48),
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


lemma Trigo_640_test : sin(5*pi/6)*cos(-pi) - sin(160*pi)*cos(5*pi/6)=sin(43*pi/6):=
begin
have : sin(5 * pi / 6) * cos(-pi) + -sin(160 * pi) * cos(5 * pi / 6) = sin(5*pi/6)*cos(-pi) - sin(160*pi)*cos(5*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -sin(160*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(5*pi/6) * cos(-pi) + sin(-pi) * cos(5*pi/6),
{
have : sin(-pi/6) = sin((5*pi/6) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(43*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_641_test : -1 + 2*(cos(pi/6)*cos(7*pi/6) + sin(pi/6)*sin(7*pi/6))**2=- cos(195*pi):=
begin
have : -1 + 2 * (sin(7 * pi / 6) * sin(pi / 6) + cos(7 * pi / 6) * cos(pi / 6)) ** 2 = -1 + 2*(cos(pi/6)*cos(7*pi/6) + sin(pi/6)*sin(7*pi/6))**2,
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
have : cos(2*pi) = - cos(195*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_642_test : cos(136*pi)=cos(94*pi):=
begin
have : - -cos(136 * pi) = cos(136*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(267*pi/2) = -cos(136*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (267*pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(267*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(94*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_643_test : sin(487*pi/2)=1 - 2 * sin(pi/2) ** 2:=
begin
have : - -sin(487 * pi / 2) = sin(487*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(205*pi/2) = -sin(487*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (205*pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(205*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (51),
focus{repeat {apply congr_arg _}},
simp,
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
rw this,
end


lemma Trigo_644_test : -3*sin(493*pi/9) + 4*sin(493*pi/9)**3=sin(281*pi/3):=
begin
have : -((-4) * sin(493 * pi / 9) ** 3 + 3 * sin(493 * pi / 9)) = -3*sin(493*pi/9) + 4*sin(493*pi/9)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(493*pi/3) = -4 * sin(493*pi/9) ** 3 + 3 * sin(493*pi/9),
{
have : sin(493*pi/3) = sin(3*(493*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(493*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(281*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_645_test (h0 : cos(pi/3)≠ 0) (h1 : (1-tan(pi/3)**2)≠ 0) (h2 : ((1-1/tan(451*pi/6)**2)*tan(451*pi/6))≠ 0) (h3 : tan(451*pi/6)≠ 0) (h4 : (1-(1/tan(451*pi/6))**2)≠ 0) : 2/((1 - 1/tan(451*pi/6)**2)*tan(451*pi/6))=- sqrt( 3 ):=
begin
have : 2 * (1 / tan(451 * pi / 6)) / (1 - (1 / tan(451 * pi / 6)) ** 2) = 2/((1 - 1/tan(451*pi/6)**2)*tan(451*pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = 1 / tan(451*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_646_test : -1 + 2*cos(pi/6)**2=-8*sin(pi/12)**2*cos(pi/12)**2 + 1:=
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


lemma Trigo_647_test : -sin(pi)*sin(226*pi/3) + cos(pi)*cos(226*pi/3)=1 / 2:=
begin
have : -sin(226 * pi / 3) * sin(pi) + cos(226 * pi / 3) * cos(pi) = -sin(pi)*sin(226*pi/3) + cos(pi)*cos(226*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(229*pi/3) = -sin(226*pi/3) * sin(pi) + cos(226*pi/3) * cos(pi),
{
have : cos(229*pi/3) = cos((226*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = cos(229*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (37),
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




lemma Trigo_649_test : 4*cos(491*pi/9)**3 - 3*cos(491*pi/9)=1 / 2:=
begin
have : cos(491*pi/3) = 4 * cos(491*pi/9) ** 3 - 3 * cos(491*pi/9),
{
have : cos(491*pi/3) = cos(3*(491*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(491*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (81),
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


lemma Trigo_650_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) (h2 : (2*sin(pi/6)**2)≠ 0) : -1 + sin(pi/3)**2/(2*sin(pi/6)**2)=sin(pi/2) * sin(pi/6) + cos(pi/2) * cos(pi/6):=
begin
have : -1 + 2 * (sin(pi / 3) / (2 * sin(pi / 6))) ** 2 = -1 + sin(pi/3)**2/(2*sin(pi/6)**2),
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


lemma Trigo_651_test : (-3*cos(-pi/18) + 4*cos(-pi/18)**3)*cos(2*pi/3) - sin(-pi/6)*sin(2*pi/3)=0:=
begin
have : (4 * cos(-pi / 18) ** 3 - 3 * cos(-pi / 18)) * cos(2 * pi / 3) - sin(-pi / 6) * sin(2 * pi / 3) = (-3*cos(-pi/18) + 4*cos(-pi/18)**3)*cos(2*pi/3) - sin(-pi/6)*sin(2*pi/3),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : -sin(2 * pi / 3) * sin(-pi / 6) + cos(2 * pi / 3) * cos(-pi / 6) = cos(-pi/6)*cos(2*pi/3) - sin(-pi/6)*sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(2*pi/3) * sin(-pi/6) + cos(2*pi/3) * cos(-pi/6),
{
have : cos(pi/2) = cos((2*pi/3) + (-pi/6)),
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


lemma Trigo_652_test (h0 : cos((496*pi/3)/2)≠ 0) (h1 : (cos(496*pi/3)+1)≠ 0) (h2 : (1+cos(496*pi/3))≠ 0) : -sin(496*pi/3)/(cos(496*pi/3) + 1)=- tan(101*pi/3):=
begin
have : -(sin(496 * pi / 3) / (1 + cos(496 * pi / 3))) = -sin(496*pi/3)/(cos(496*pi/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(248*pi/3) = sin(496*pi/3) / ( 1 + cos(496*pi/3) ),
{
have : tan(248*pi/3) = tan((496*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = -tan(248*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = - tan(101*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_653_test : (-3*cos(2555*pi/18) + 4*cos(2555*pi/18)**3)*sin(-pi/2)=- sin(2*pi/3) / 2 + sin(-pi/3) / 2:=
begin
have : ((-3) * cos(2555 * pi / 18) + 4 * cos(2555 * pi / 18) ** 3) * sin(-pi / 2) = (-3*cos(2555*pi/18) + 4*cos(2555*pi/18)**3)*sin(-pi/2),
{
field_simp at *,
},
have : cos(pi/18) = cos(2555*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/18) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) * (4 * cos(pi / 18) ** 3 - 3 * cos(pi / 18)) = (-3*cos(pi/18) + 4*cos(pi/18)**3)*sin(-pi/2),
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


lemma Trigo_654_test : -cos(1069*pi/6)=cos(1279*pi/6):=
begin
have : sin(-pi/3) = -cos(1069*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(439*pi/6) = cos(1279*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (439*pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = cos(439*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_655_test : 4*cos(4373*pi/36)**3 - 3*cos(4373*pi/36)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : (-4) * (-cos(4373 * pi / 36)) ** 3 + 3 * -cos(4373 * pi / 36) = 4*cos(4373*pi/36)**3 - 3*cos(4373*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) = -cos(4373*pi/36),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/36) (60),
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


lemma Trigo_656_test (h0 : sin(-pi/3)≠ 0) (h1 : (2*sin(-pi/3))≠ 0) (h2 : (4*sin(-pi/3)**2)≠ 0) (h3 : cos(-2*pi/3)≠ 0) (h4 : (2*cos((-2)*pi/3))≠ 0) (h5 : (16*sin(-pi/3)**2*cos(-2*pi/3)**2)≠ 0) : sin(-4*pi/3)**2/(16*sin(-pi/3)**2*cos(-2*pi/3)**2)=1 - sin(-pi/3) ** 2:=
begin
have : (sin((-4) * pi / 3) / (2 * cos((-2) * pi / 3))) ** 2 / (4 * sin(-pi / 3) ** 2) = sin(-4*pi/3)**2/(16*sin(-pi/3)**2*cos(-2*pi/3)**2),
{
field_simp at *,
repeat {left},
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
have : (sin((-2) * pi / 3) / (2 * sin(-pi / 3))) ** 2 = sin(-2*pi/3)**2/(4*sin(-pi/3)**2),
{
field_simp at *,
repeat {left},
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
have : cos(-pi/3) ** 2 = 1 - sin(-pi/3) ** 2,
{
rw cos_sq',
},
rw this,
end


lemma Trigo_657_test : sin(-4*pi/3)*sin(2*pi)/2 - cos(-4*pi/3)*cos(2*pi)/2 + 1/2=1 - cos(pi/3) ** 2:=
begin
have : 1 / 2 - (-sin((-4) * pi / 3) * sin(2 * pi) + cos((-4) * pi / 3) * cos(2 * pi)) / 2 = sin(-4*pi/3)*sin(2*pi)/2 - cos(-4*pi/3)*cos(2*pi)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(-4*pi/3) * sin(2*pi) + cos(-4*pi/3) * cos(2*pi),
{
have : cos(2*pi/3) = cos((-4*pi/3) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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
have : sin(pi/3) ** 2 = 1 - cos(pi/3) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_658_test (h0 : cos((129*pi/2)/2)≠ 0) (h1 : (cos(129*pi/2)+1)≠ 0) (h2 : (1+cos(129*pi/2))≠ 0) : sin(129*pi/2)/(cos(129*pi/2) + 1)=1:=
begin
have : sin(129 * pi / 2) / (1 + cos(129 * pi / 2)) = sin(129*pi/2)/(cos(129*pi/2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(129*pi/4) = sin(129*pi/2) / ( 1 + cos(129*pi/2) ),
{
have : tan(129*pi/4) = tan((129*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = tan(129*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (pi/4) (32),
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


lemma Trigo_659_test : -cos(8*pi)=-3*cos(529*pi/3) + 4*cos(529*pi/3)**3:=
begin
have : (-4) * (-cos(529 * pi / 3)) ** 3 + 3 * -cos(529 * pi / 3) = -3*cos(529*pi/3) + 4*cos(529*pi/3)**3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = -cos(529*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = -cos(8*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (3),
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


lemma Trigo_660_test (h0 : sin(122*pi/3)≠ 0) (h1 : (2*sin(122*pi/3))≠ 0) : -sin(244*pi/3)/(2*sin(122*pi/3))=1 / 2:=
begin
have : -(sin(244 * pi / 3) / (2 * sin(122 * pi / 3))) = -sin(244*pi/3)/(2*sin(122*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(122*pi/3) = sin(244*pi/3) / ( 2 * sin(122*pi/3) ),
{
have : sin(244*pi/3) = sin(2*(122*pi/3)),
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
have : sin(pi/6) = -cos(122*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (20),
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


lemma Trigo_661_test (h0 : cos(-pi/3)≠ 0) (h1 : (2*cos(-pi/3)**3)≠ 0) (h2 : (2*cos(-pi/3))≠ 0) : 3*sin(-2*pi/3)/(2*cos(-pi/3)) - sin(-2*pi/3)**3/(2*cos(-pi/3)**3)=- cos(109*pi/2):=
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
have : sin(-pi) = - cos(109*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_663_test (h0 : sin(-pi/3)≠ 0) (h1 : (2*sin(-pi/3))≠ 0) (h2 : sin(-pi/3)≠ 0) : sin(323*pi/3) + sin(-pi)=sin(-2*pi/3)**2/sin(-pi/3):=
begin
have : 2 * sin((-2) * pi / 3) * (sin((-2) * pi / 3) / (2 * sin(-pi / 3))) = sin(-2*pi/3)**2/sin(-pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-pi) - -sin(323 * pi / 3) = sin(323*pi/3) + sin(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(323*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (54),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_664_test (h0 : cos(pi)≠ 0) (h1 : sin(65*pi/2)≠ 0) (h2 : -sin(65*pi/2)≠ 0) : -sin(pi)/sin(65*pi/2)=- tan(15*pi):=
begin
have : sin(pi) / -sin(65 * pi / 2) = -sin(pi)/sin(65*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(65*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (16),
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
have : tan(pi) = - tan(15*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_665_test : -cos(2557*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(1603*pi/12) = cos(2557*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1603*pi/12) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(1603*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (66),
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


lemma Trigo_666_test : -cos(161*pi/3)=1 - 2*(-4*sin(pi/9)**3 + 3*sin(pi/9))**2:=
begin
have : cos(2*pi/3) = -cos(161*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi/3) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * ((-4) * sin(pi / 9) ** 3 + 3 * sin(pi / 9)) ** 2 = 1 - 2*(-4*sin(pi/9)**3 + 3*sin(pi/9))**2,
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
conv {to_rhs, rw ← this,},
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
rw this,
end


lemma Trigo_667_test (h0 : sin(pi/2)≠ 0) (h1 : (2*sin(pi/2))≠ 0) : -cos(279*pi/2)=-cos(389*pi/2)/(2*sin(pi/2)):=
begin
have : sin(pi) = -cos(389*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -cos(279*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/2) (69),
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


lemma Trigo_668_test (h0 : sin(439*pi/6)≠ 0) (h1 : (2*sin(439*pi/6))≠ 0) : -sin(439*pi/3)/(2*sin(439*pi/6))=sqrt( 3 ) / 2:=
begin
have : -(sin(439 * pi / 3) / (2 * sin(439 * pi / 6))) = -sin(439*pi/3)/(2*sin(439*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(439*pi/6) = sin(439*pi/3) / ( 2 * sin(439*pi/6) ),
{
have : sin(439*pi/3) = sin(2*(439*pi/6)),
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
have : sin(2*pi/3) = -cos(439*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (36),
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


lemma Trigo_669_test : sin(18*pi)=0:=
begin
have : - -sin(18 * pi) = sin(18*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(90*pi) = -sin(18*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (90*pi) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = -sin(90*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi) (44),
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


lemma Trigo_670_test : (1 - 2*sin(-pi/6)**2)*cos(67*pi)=sin(-pi/6) / 2 + sin(-5*pi/6) / 2:=
begin
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
conv {to_lhs, rw ← this,},
have : cos(67 * pi) * cos(-pi / 3) = cos(-pi/3)*cos(67*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(67*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(-pi/3) = sin(-pi/6) / 2 + sin(-5*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((-pi/2) + (-pi/3)) = sin(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (-pi/3)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_671_test : -sin(-pi/6) + sin(217*pi/2)=2*sin(pi/3)*cos(157*pi/6):=
begin
have : sin(217 * pi / 2) - sin(-pi / 6) = -sin(-pi/6) + sin(217*pi/2),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(217*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(157*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) - sin(-pi/6) = 2 * sin(pi/3) * cos(pi/6),
{
rw sin_sub_sin,
have : cos(((pi/2) + (-pi/6))/2) = cos(pi/6),
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
},
rw this,
end


lemma Trigo_672_test : 4*cos(451*pi/6)**3 - 3*cos(451*pi/6)=- sin(137*pi):=
begin
have : (-4) * (-cos(451 * pi / 6)) ** 3 + 3 * -cos(451 * pi / 6) = 4*cos(451*pi/6)**3 - 3*cos(451*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(451*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (37),
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
have : sin(pi) = - sin(137*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_673_test : -3*cos(289*pi/6) + 4*cos(289*pi/6)**3=0:=
begin
have : 4 * cos(289 * pi / 6) ** 3 - 3 * cos(289 * pi / 6) = -3*cos(289*pi/6) + 4*cos(289*pi/6)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(289*pi/2) = 4 * cos(289*pi/6) ** 3 - 3 * cos(289*pi/6),
{
have : cos(289*pi/2) = cos(3*(289*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(289*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (71),
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


lemma Trigo_674_test : cos(174*pi)=1 - 2*sin(56*pi)**2:=
begin
have : cos(4*pi) = cos(174*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (4*pi) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (-sin(56 * pi)) ** 2 = 1 - 2*sin(56*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -sin(56*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (29),
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


lemma Trigo_675_test : -sin(2*pi)*sin(759*pi/4) + cos(2*pi)*cos(9*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(2 * pi) * -sin(759 * pi / 4) + cos(2 * pi) * cos(9 * pi / 4) = -sin(2*pi)*sin(759*pi/4) + cos(2*pi)*cos(9*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(9*pi/4) = -sin(759*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (9*pi/4) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(9 * pi / 4) * sin(2 * pi) + cos(9 * pi / 4) * cos(2 * pi) = sin(2*pi)*sin(9*pi/4) + cos(2*pi)*cos(9*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(9*pi/4) * sin(2*pi) + cos(9*pi/4) * cos(2*pi),
{
have : cos(pi/4) = cos((9*pi/4) - (2*pi)),
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


lemma Trigo_676_test : 4*sin(979*pi/36)**3 - 3*sin(979*pi/36)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -((-4) * sin(979 * pi / 36) ** 3 + 3 * sin(979 * pi / 36)) = 4*sin(979*pi/36)**3 - 3*sin(979*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(979*pi/12) = -4 * sin(979*pi/36) ** 3 + 3 * sin(979*pi/36),
{
have : sin(979*pi/12) = sin(3*(979*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(979*pi/12),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (40),
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


lemma Trigo_677_test (h0 : tan(335*pi/4)≠ 0) (h1 : (1/tan(31*pi/4))≠ 0) (h2 : tan(31*pi/4)≠ 0) : tan(31*pi/4)=- 1:=
begin
have : 1 / (1 / tan(31 * pi / 4)) = tan(31*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(335*pi/4) = 1 / tan(31*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (335*pi/4) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/4) = 1 / tan(335*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/4) (84),
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


lemma Trigo_678_test : cos(-163*pi/3)=1 - 2 * sin(-pi/6) ** 2:=
begin
have : - -cos((-163) * pi / 3) = cos(-163*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(563*pi/6) = -cos(-163*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (563*pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(563*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (46),
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


lemma Trigo_679_test : cos(-pi/2)*cos(9*pi/2) - sin(-pi/2)*sin(9*pi/2)=-cos(375*pi/2)**2 + cos(2*pi)**2:=
begin
have : -sin(9 * pi / 2) * sin(-pi / 2) + cos(9 * pi / 2) * cos(-pi / 2) = cos(-pi/2)*cos(9*pi/2) - sin(-pi/2)*sin(9*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi) = -sin(9*pi/2) * sin(-pi/2) + cos(9*pi/2) * cos(-pi/2),
{
have : cos(4*pi) = cos((9*pi/2) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -(-cos(375 * pi / 2)) ** 2 + cos(2 * pi) ** 2 = -cos(375*pi/2)**2 + cos(2*pi)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -cos(375*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (94),
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


lemma Trigo_680_test : sin(pi/2)*sin(7*pi/6) + sin(119*pi)*cos(7*pi/6)=- 1 / 2:=
begin
have : cos(pi/2) = sin(119*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_681_test : 2*cos(pi/8)*cos(931*pi/8)=sqrt( 2 ) / 2:=
begin
have : 2 * cos(931 * pi / 8) * cos(pi / 8) = 2*cos(pi/8)*cos(931*pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = cos(931*pi/8),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/8) (58),
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


lemma Trigo_682_test : cos(-2*pi)*cos(11*pi) + sin(-2*pi)*sin(11*pi)=2 * cos(-pi/2) ** 2 - 1:=
begin
have : sin(11 * pi) * sin((-2) * pi) + cos(11 * pi) * cos((-2) * pi) = cos(-2*pi)*cos(11*pi) + sin(-2*pi)*sin(11*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi) = sin(11*pi) * sin(-2*pi) + cos(11*pi) * cos(-2*pi),
{
have : cos(13*pi) = cos((11*pi) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(13*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (7),
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


lemma Trigo_683_test : -2*cos(-pi/4)**2 - sin(427*pi/6) + 1=- 2 * sin(5*pi/12) * sin(-pi/12):=
begin
have : -(2 * cos(-pi / 4) ** 2 - 1) - sin(427 * pi / 6) = -2*cos(-pi/4)**2 - sin(427*pi/6) + 1,
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
have : -sin(427 * pi / 6) - cos(-pi / 2) = -cos(-pi/2) - sin(427*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(427*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) - cos(-pi/2) = - 2 * sin(5*pi/12) * sin(-pi/12),
{
rw cos_sub_cos,
have : sin(((pi/3) + (-pi/2))/2) = sin(-pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (-pi/2))/2) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_684_test (h0 : cos(3*pi/4)≠ 0) (h1 : (-1+2*cos(3*pi/8)**2)≠ 0) (h2 : (2*cos(3*pi/8)**2-1)≠ 0) : sin(3*pi/4)/(-1 + 2*cos(3*pi/8)**2)=- 1:=
begin
have : sin(3 * pi / 4) / (2 * cos(3 * pi / 8) ** 2 - 1) = sin(3*pi/4)/(-1 + 2*cos(3*pi/8)**2),
{
field_simp at *,
repeat {left},
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


lemma Trigo_685_test : (-sin(-pi/6)*cos(99*pi) + sin(99*pi)*cos(-pi/6))**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : (sin(99 * pi) * cos(-pi / 6) - sin(-pi / 6) * cos(99 * pi)) ** 2 = (-sin(-pi/6)*cos(99*pi) + sin(99*pi)*cos(-pi/6))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(595*pi/6) = sin(99*pi) * cos(-pi/6) - sin(-pi/6) * cos(99*pi),
{
have : sin(595*pi/6) = sin((99*pi) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(595 * pi / 6)) ** 2 = sin(595*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(595*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (49),
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


lemma Trigo_686_test : -cos(-55*pi/2)=- sin(35*pi):=
begin
have : -cos((-55) * pi / 2) = -cos(-55*pi/2),
{
field_simp at *,
},
have : sin(54*pi) = cos(-55*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (54*pi) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -sin(54*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(35*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_687_test : sin(-125*pi/2)**2=1 / 2 - cos(pi) / 2:=
begin
have : sin((-125) * pi / 2) ** 2 = sin(-125*pi/2)**2,
{
field_simp at *,
},
have : sin(359*pi/2) = sin(-125*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (359*pi/2) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(359 * pi / 2)) ** 2 = sin(359*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(359*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (89),
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


lemma Trigo_688_test : sin(10*pi/3) - 4*sin(pi/6)**3 + 3*sin(pi/6)=2 * sin(pi/12) * cos(-5*pi/12):=
begin
have : sin(10 * pi / 3) + ((-4) * sin(pi / 6) ** 3 + 3 * sin(pi / 6)) = sin(10*pi/3) - 4*sin(pi/6)**3 + 3*sin(pi/6),
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
have : sin(-pi/3) = sin(10*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) + sin(pi/2) = 2 * sin(pi/12) * cos(-5*pi/12),
{
rw sin_add_sin,
have : sin(((-pi/3) + (pi/2))/2) = sin(pi/12),
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
},
rw this,
end


lemma Trigo_689_test (h0 : cos((pi/2)/2)≠ 0) (h1 : (1+cos(pi/2))≠ 0) (h2 : (cos(pi/2)+1)≠ 0) : sin(261*pi/2)/(cos(pi/2) + 1)=1:=
begin
have : sin(pi/2) = sin(261*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (65),
focus{repeat {apply congr_arg _}},
simp,
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
have : tan(pi/4) = 1,
{
rw tan_pi_div_four,
},
rw this,
end


lemma Trigo_690_test : -cos(301*pi/6) + 2*sin(-pi/12)*cos(-pi/12)=2 * sin(-pi/4) * cos(pi/12):=
begin
have : sin(pi/3) = cos(301*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 12) * cos(-pi / 12) - sin(pi / 3) = -sin(pi/3) + 2*sin(-pi/12)*cos(-pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(-pi/6) - sin(pi/3) = 2 * sin(-pi/4) * cos(pi/12),
{
rw sin_sub_sin,
have : cos(((-pi/6) + (pi/3))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi/6) - (pi/3))/2) = sin(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_691_test : -sin(59*pi/6)=cos(pi/3):=
begin
have : 2 * (cos(pi / 3) / 2 + 1 / 2) - 1 = cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -sin(59*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (4),
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


lemma Trigo_692_test (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : sin(284*pi/3)/(2*cos(pi/3))=cos(13*pi/6):=
begin
have : sin(2*pi/3) = sin(284*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (47),
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
have : sin(pi/3) = cos(13*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_694_test : -4*sin(47*pi/18)**3 + 3*sin(47*pi/18)=- 1 / 2:=
begin
have : (-4) * sin(47 * pi / 18) ** 3 + 3 * sin(47 * pi / 18) = -4*sin(47*pi/18)**3 + 3*sin(47*pi/18),
{
field_simp at *,
},
have : sin(47*pi/6) = -4 * sin(47*pi/18) ** 3 + 3 * sin(47*pi/18),
{
have : sin(47*pi/6) = sin(3*(47*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(47*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (4),
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


lemma Trigo_695_test : -cos(631*pi/6)=-sin(190*pi/3):=
begin
have : sin(71*pi/3) = sin(190*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (71*pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = -cos(631*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = - sin(71*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_696_test : (sin(-pi/3)*cos(-5*pi/3) + sin(-5*pi/3)*cos(-pi/3))*sin(43*pi)=- sin(3*pi/2) / 2 + sin(-5*pi/2) / 2:=
begin
have : (sin(-pi / 3) * cos((-5) * pi / 3) + sin((-5) * pi / 3) * cos(-pi / 3)) * sin(43 * pi) = (sin(-pi/3)*cos(-5*pi/3) + sin(-5*pi/3)*cos(-pi/3))*sin(43*pi),
{
field_simp at *,
},
have : cos(-pi/2) = sin(43*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-5) * pi / 3) * cos(-pi / 3) + sin(-pi / 3) * cos((-5) * pi / 3)) * cos(-pi / 2) = (sin(-pi/3)*cos(-5*pi/3) + sin(-5*pi/3)*cos(-pi/3))*cos(-pi/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-5*pi/3) * cos(-pi/3) + sin(-pi/3) * cos(-5*pi/3),
{
have : sin(-2*pi) = sin((-5*pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_697_test : -1 + 2*(-sin(-pi/6)*sin(7*pi/24) + cos(-pi/6)*cos(7*pi/24))**2=sqrt( 2 ) / 2:=
begin
have : -1 + 2 * (-sin(7 * pi / 24) * sin(-pi / 6) + cos(7 * pi / 24) * cos(-pi / 6)) ** 2 = -1 + 2*(-sin(-pi/6)*sin(7*pi/24) + cos(-pi/6)*cos(7*pi/24))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(7*pi/24) * sin(-pi/6) + cos(7*pi/24) * cos(-pi/6),
{
have : cos(pi/8) = cos((7*pi/24) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_698_test : -tan(-28*pi/3)=sqrt( 3 ):=
begin
have : -tan((-28) * pi / 3) = -tan(-28*pi/3),
{
field_simp at *,
},
have : tan(214*pi/3) = -tan(-28*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (214*pi/3) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = tan(214*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (pi/3) (71),
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


lemma Trigo_699_test : -3*cos(pi/9) + 4*cos(pi/9)**3=2*sin(973*pi/12)*cos(973*pi/12):=
begin
have : sin(973*pi/6) = 2 * sin(973*pi/12) * cos(973*pi/12),
{
have : sin(973*pi/6) = sin(2*(973*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
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
have : cos(pi/3) = sin(973*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_701_test : cos(-pi)=-sin(266*pi/3)*cos(pi/6) + sin(-177*pi/2)/2 + sin(533*pi/6)/2:=
begin
have : -sin(266 * pi / 3) * cos(pi / 6) + (sin((-177) * pi / 2) / 2 + sin(533 * pi / 6) / 2) = -sin(266*pi/3)*cos(pi/6) + sin(-177*pi/2)/2 + sin(533*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) * cos(266*pi/3) = sin(-177*pi/2) / 2 + sin(533*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/6) + (266*pi/3)) = sin(533*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (266*pi/3)) = sin(-177*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (sin(pi/6) * cos(266*pi/3)) = sin(pi/6)*cos(266*pi/3),
{
ring,
},
have : -(sin(266 * pi / 3) * cos(pi / 6) - sin(pi / 6) * cos(266 * pi / 3)) = -sin(266*pi/3)*cos(pi/6) + sin(pi/6)*cos(266*pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(177*pi/2) = sin(266*pi/3) * cos(pi/6) - sin(pi/6) * cos(266*pi/3),
{
have : sin(177*pi/2) = sin((266*pi/3) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = - sin(177*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_702_test : sin(pi/3)*cos(pi/2) + sin(pi/2)*cos(pi/3)=sin(pi)*cos(-pi/6) - sin(-pi/6)*sin(273*pi/2):=
begin
have : sin(5*pi/6) = sin(pi/3) * cos(pi/2) + sin(pi/2) * cos(pi/3),
{
have : sin(5*pi/6) = sin((pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 6) * -sin(273 * pi / 2) + sin(pi) * cos(-pi / 6) = sin(pi)*cos(-pi/6) - sin(-pi/6)*sin(273*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = -sin(273*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/6) = sin(-pi/6) * cos(pi) + sin(pi) * cos(-pi/6),
{
have : sin(5*pi/6) = sin((-pi/6) + (pi)),
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


lemma Trigo_703_test (h0 : (-sin(5*pi/2)*sin(-pi/2)+cos(5*pi/2)*cos(-pi/2))≠ 0) (h1 : (cos(-pi/2)*cos(5*pi/2)-sin(-pi/2)*sin(5*pi/2))≠ 0) : tan(2*pi)=-sin(90*pi)/(cos(-pi/2)*cos(5*pi/2) - sin(-pi/2)*sin(5*pi/2)):=
begin
have : sin(2*pi) = -sin(90*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2 * pi) / (-sin(5 * pi / 2) * sin(-pi / 2) + cos(5 * pi / 2) * cos(-pi / 2)) = sin(2*pi)/(cos(-pi/2)*cos(5*pi/2) - sin(-pi/2)*sin(5*pi/2)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -sin(5*pi/2) * sin(-pi/2) + cos(5*pi/2) * cos(-pi/2),
{
have : cos(2*pi) = cos((5*pi/2) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : tan(2*pi) = sin(2*pi) / cos(2*pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_704_test : -2*sin(pi)*sin(539*pi/4)*cos(-pi/4)=cos(-3*pi/2) / 2 - cos(pi/2) / 2:=
begin
have : 2 * -sin(539 * pi / 4) * sin(pi) * cos(-pi / 4) = -2*sin(pi)*sin(539*pi/4)*cos(-pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -sin(539*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/4) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 4) * cos(-pi / 4) * sin(pi) = 2*sin(-pi/4)*sin(pi)*cos(-pi/4),
{
field_simp at *,
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


lemma Trigo_705_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) (h2 : (2*-cos(57*pi/2))≠ 0) (h3 : (2*cos(57*pi/2))≠ 0) : -sin(pi)/(2*cos(57*pi/2)) + sin(pi/6)=2 * sin(pi/3) * cos(-pi/6):=
begin
have : sin(pi / 6) + sin(pi) / (2 * -cos(57 * pi / 2)) = -sin(pi)/(2*cos(57*pi/2)) + sin(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -cos(57*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (14),
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
have : sin(pi/6) + sin(pi/2) = 2 * sin(pi/3) * cos(-pi/6),
{
rw sin_add_sin,
have : sin(((pi/6) + (pi/2))/2) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/6) - (pi/2))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_706_test (h0 : sin(50*pi/3)≠ 0) (h1 : (2*sin(50*pi/3))≠ 0) : -sin(100*pi/3)/(2*sin(50*pi/3))=1 / 2:=
begin
have : -(sin(100 * pi / 3) / (2 * sin(50 * pi / 3))) = -sin(100*pi/3)/(2*sin(50*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(50*pi/3) = sin(100*pi/3) / ( 2 * sin(50*pi/3) ),
{
have : sin(100*pi/3) = sin(2*(50*pi/3)),
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
have : sin(pi/6) = -cos(50*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (8),
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


lemma Trigo_707_test : -(1 - 2*sin(-pi/6)**2)*cos(17*pi)=sin(5*pi/6) / 2 + sin(pi/6) / 2:=
begin
have : (1 - 2 * sin(-pi / 6) ** 2) * -cos(17 * pi) = -(1 - 2*sin(-pi/6)**2)*cos(17*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(17*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 2) * (1 - 2 * sin(-pi / 6) ** 2) = (1 - 2*sin(-pi/6)**2)*sin(pi/2),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) * cos(-pi/3) = sin(5*pi/6) / 2 + sin(pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/2) + (-pi/3)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/2) - (-pi/3)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_708_test : sin(2*pi/3)*cos(pi/2) - 2*sin(pi/4)*cos(pi/4)*cos(2*pi/3)=- sin(1171*pi/6):=
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
have : sin(pi/6) = - sin(1171*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_709_test : sin(250*pi/3)=sin(-pi/3)*cos(2*pi) - (1 - 2*sin(-pi/6)**2)*sin(2*pi):=
begin
have : sin(-7*pi/3) = sin(250*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-7*pi/3) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 3) * cos(2 * pi) - sin(2 * pi) * (1 - 2 * sin(-pi / 6) ** 2) = sin(-pi/3)*cos(2*pi) - (1 - 2*sin(-pi/6)**2)*sin(2*pi),
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


lemma Trigo_710_test : sin(pi/3)*cos(403*pi/12) + sin(5*pi/12)*cos(pi/3)=sqrt( 2 ) / 2:=
begin
have : cos(5*pi/12) = cos(403*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/12) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 12) * cos(pi / 3) + sin(pi / 3) * cos(5 * pi / 12) = sin(pi/3)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(5*pi/12) * cos(pi/3) + sin(pi/3) * cos(5*pi/12),
{
have : sin(3*pi/4) = sin((5*pi/12) + (pi/3)),
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


lemma Trigo_711_test : 1 - 2*sin(1335*pi/8)**2=sqrt( 2 ) / 2:=
begin
have : sin(pi/8) = sin(1335*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/8) (83),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_712_test : -sin(1024*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(430*pi/3) = sin(1024*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (430*pi/3) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(430*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/3) (72),
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


lemma Trigo_713_test : sin(-pi/6) + 2*sin(pi/2)*cos(11*pi/2)=2 * sin(5*pi/12) * cos(7*pi/12):=
begin
have : cos(pi/2) = cos(11*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 2) * cos(pi / 2) + sin(-pi / 6) = sin(-pi/6) + 2*sin(pi/2)*cos(pi/2),
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


lemma Trigo_714_test (h0 : cos(-5*pi/6)≠ 0) (h1 : cos(pi/6)≠ 0) (h2 : (tan(-5*pi/6)*tan(pi/6)+1)≠ 0) (h3 : (1+tan((-5)*pi/6)*tan(pi/6))≠ 0) (h4 : cos(pi/6)≠ 0) (h5 : cos(-5*pi/6)≠ 0) (h6 : ((tan(-5*pi/6)*tan(pi/6)+1)*cos(-5*pi/6)*cos(pi/6))≠ 0) (h7 : (cos(pi/6)*cos((-5)*pi/6))≠ 0) (h8 : (tan((-5)*pi/6)*tan(pi/6)+1)≠ 0) : -sin(pi)/((tan(-5*pi/6)*tan(pi/6) + 1)*cos(-5*pi/6)*cos(pi/6))=- tan(99*pi):=
begin
have : (-1) * (sin(pi) / (cos(pi / 6) * cos((-5) * pi / 6))) / (tan((-5) * pi / 6) * tan(pi / 6) + 1) = -sin(pi)/((tan(-5*pi/6)*tan(pi/6) + 1)*cos(-5*pi/6)*cos(pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) - tan(-5*pi/6) = sin(pi) / ( cos(pi/6) * cos(-5*pi/6) ),
{
rw tan_sub_tan',
have : sin((pi/6) - (-5*pi/6)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -1*(tan(pi/6) - tan(-5*pi/6)) = (-tan(pi/6)+tan(-5*pi/6)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan((-5) * pi / 6) - tan(pi / 6)) / (1 + tan((-5) * pi / 6) * tan(pi / 6)) = (-tan(pi/6) + tan(-5*pi/6))/(tan(-5*pi/6)*tan(pi/6) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = ( tan(-5*pi/6) - tan(pi/6) ) / ( 1 + tan(-5*pi/6) * tan(pi/6) ),
{
have : tan(-pi) = tan((-5*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - tan(99*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_715_test : -cos(967*pi/6)=cos(pi/2)*cos(257*pi/3) - sin(pi/2)*sin(257*pi/3):=
begin
have : sin(pi/3) = -cos(967*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(257 * pi / 3) * sin(pi / 2) + cos(257 * pi / 3) * cos(pi / 2) = cos(pi/2)*cos(257*pi/3) - sin(pi/2)*sin(257*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(517*pi/6) = -sin(257*pi/3) * sin(pi/2) + cos(257*pi/3) * cos(pi/2),
{
have : cos(517*pi/6) = cos((257*pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = cos(517*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_716_test : -sin(131*pi)/2 - sin(130*pi)/2=cos(3*pi/2) / 2 + cos(pi/2) / 2:=
begin
have : -(sin(131 * pi) / 2 + sin(130 * pi) / 2) = -sin(131*pi)/2 - sin(130*pi)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(261*pi/2) * cos(-pi/2) = sin(131*pi) / 2 + sin(130*pi) / 2,
{
rw sin_mul_cos,
have : sin((261*pi/2) + (-pi/2)) = sin(130*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((261*pi/2) - (-pi/2)) = sin(131*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(261*pi/2) * cos(-pi/2)) = -sin(261*pi/2)*cos(-pi/2),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi) = -sin(261*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (65),
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


lemma Trigo_717_test (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(-pi/6)*tan(-pi/3))≠ 0) (h3 : (tan(-pi/3)*tan(-pi/6)+1)≠ 0) (h4 : cos(-pi/3)≠ 0) (h5 : cos(-pi/6)≠ 0) (h6 : (cos(-pi/3)*cos(-pi/6))≠ 0) (h7 : ((tan(-pi/3)*tan(-pi/6)+1)*cos(-pi/3)*cos(-pi/6))≠ 0) : -sin(-pi/6)/((tan(-pi/3)*tan(-pi/6) + 1)*cos(-pi/3)*cos(-pi/6))=sqrt( 3 ) / 3:=
begin
have : (-1) * (sin(-pi / 6) / (cos(-pi / 3) * cos(-pi / 6))) / (tan(-pi / 3) * tan(-pi / 6) + 1) = -sin(-pi/6)/((tan(-pi/3)*tan(-pi/6) + 1)*cos(-pi/3)*cos(-pi/6)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) - tan(-pi/6) = sin(-pi/6) / ( cos(-pi/3) * cos(-pi/6) ),
{
rw tan_sub_tan',
have : sin((-pi/3) - (-pi/6)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -1*(tan(-pi/3) - tan(-pi/6)) = (tan(-pi/6)-tan(-pi/3)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan(-pi / 6) - tan(-pi / 3)) / (1 + tan(-pi / 6) * tan(-pi / 3)) = (tan(-pi/6) - tan(-pi/3))/(tan(-pi/3)*tan(-pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(-pi/6) - tan(-pi/3) ) / ( 1 + tan(-pi/6) * tan(-pi/3) ),
{
have : tan(pi/6) = tan((-pi/6) - (-pi/3)),
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


lemma Trigo_718_test : sin(-17*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(793*pi/6)=- 4 * sin(-pi) ** 3 + 3 * sin(-pi):=
begin
have : sin((-17) * pi / 6) * cos(-pi / 6) + sin(-pi / 6) * -cos(793 * pi / 6) = sin(-17*pi/6)*cos(-pi/6) - sin(-pi/6)*cos(793*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-17*pi/6) = -cos(793*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-17*pi/6) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-17) * pi / 6) * cos(-pi / 6) + sin(-pi / 6) * cos((-17) * pi / 6) = sin(-17*pi/6)*cos(-pi/6) + sin(-pi/6)*cos(-17*pi/6),
{
field_simp at *,
},
have : sin(-3*pi) = sin(-17*pi/6) * cos(-pi/6) + sin(-pi/6) * cos(-17*pi/6),
{
have : sin(-3*pi) = sin((-17*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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


lemma Trigo_719_test (h0 : cos(179*pi/3)≠ 0) : -sin(179*pi/3)/cos(179*pi/3)=- tan(68*pi/3):=
begin
have : -(sin(179 * pi / 3) / cos(179 * pi / 3)) = -sin(179*pi/3)/cos(179*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(179*pi/3) = sin(179*pi/3) / cos(179*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = -tan(179*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = - tan(68*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_720_test : 4*cos(1133*pi/18)**3 - 3*cos(1133*pi/18)=- sin(128*pi/3):=
begin
have : cos(1133*pi/6) = 4 * cos(1133*pi/18) ** 3 - 3 * cos(1133*pi/18),
{
have : cos(1133*pi/6) = cos(3*(1133*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(1133*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = - sin(128*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_721_test : sin(-pi)*cos(741*pi/4) + cos(-pi)*cos(-3*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(-pi) * cos(741 * pi / 4) + cos(-pi) * cos((-3) * pi / 4) = sin(-pi)*cos(741*pi/4) + cos(-pi)*cos(-3*pi/4),
{
field_simp at *,
},
have : sin(-3*pi/4) = cos(741*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-3*pi/4) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-3) * pi / 4) * sin(-pi) + cos((-3) * pi / 4) * cos(-pi) = sin(-pi)*sin(-3*pi/4) + cos(-pi)*cos(-3*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = sin(-3*pi/4) * sin(-pi) + cos(-3*pi/4) * cos(-pi),
{
have : cos(pi/4) = cos((-3*pi/4) - (-pi)),
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


lemma Trigo_722_test : -sin(445*pi/3)=-sin(-pi/3)*sin(163*pi/2) + sin(2*pi)*cos(-pi/3):=
begin
have : sin(5*pi/3) = -sin(445*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/3) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) * cos(-pi / 3) + sin(-pi / 3) * -sin(163 * pi / 2) = -sin(-pi/3)*sin(163*pi/2) + sin(2*pi)*cos(-pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -sin(163*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(5*pi/3) = sin(2*pi) * cos(-pi/3) + sin(-pi/3) * cos(2*pi),
{
have : sin(5*pi/3) = sin((2*pi) + (-pi/3)),
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


lemma Trigo_723_test : -cos(409*pi/2)=- 4 * sin(-pi/3) ** 3 + 3 * sin(-pi/3):=
begin
have : sin(115*pi) = cos(409*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (115*pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -sin(115*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (57),
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


lemma Trigo_724_test : sin(25*pi/6)**2=1 - (-1 + 2*cos(-pi/12)**2)**2:=
begin
have : 1 - (2 * cos(-pi / 12) ** 2 - 1) ** 2 = 1 - (-1 + 2*cos(-pi/12)**2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : (-sin(25 * pi / 6)) ** 2 = sin(25*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(25*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (2),
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


lemma Trigo_725_test : sin(386*pi/3)=2*(sin(-2*pi)*sin(-11*pi/6) + cos(-2*pi)*cos(-11*pi/6))*sin(pi/6):=
begin
have : sin(pi/3) = sin(386*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 6) * (sin((-11) * pi / 6) * sin((-2) * pi) + cos((-11) * pi / 6) * cos((-2) * pi)) = 2*(sin(-2*pi)*sin(-11*pi/6) + cos(-2*pi)*cos(-11*pi/6))*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = sin(-11*pi/6) * sin(-2*pi) + cos(-11*pi/6) * cos(-2*pi),
{
have : cos(pi/6) = cos((-11*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
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


lemma Trigo_726_test : (sin(2*pi/3)*cos(-pi/2) + 2*sin(-pi/4)*cos(-pi/4)*cos(2*pi/3))**2 + cos(pi/6)**2=1:=
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
conv {to_lhs, rw ← this,},
have : sin(pi/6) ** 2 + cos(pi/6) ** 2 = 1,
{
rw sin_sq_add_cos_sq,
},
rw this,
end


lemma Trigo_727_test (h0 : cos(pi)≠ 0) (h1 : sin(311*pi/2)≠ 0) : (sin(pi/6)*cos(5*pi/6) + sin(5*pi/6)*cos(pi/6))/sin(311*pi/2)=tan(pi):=
begin
have : cos(pi) = sin(311*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(5 * pi / 6) * cos(pi / 6) + sin(pi / 6) * cos(5 * pi / 6)) / cos(pi) = (sin(pi/6)*cos(5*pi/6) + sin(5*pi/6)*cos(pi/6))/cos(pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(5*pi/6) * cos(pi/6) + sin(pi/6) * cos(5*pi/6),
{
have : sin(pi) = sin((5*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) / cos(pi) = tan(pi),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_728_test : sin(1051*pi/6)*cos(pi/6) - sin(pi/6)*cos(1051*pi/6)=2 * sin(2*pi) * cos(2*pi):=
begin
have : sin(175*pi) = sin(1051*pi/6) * cos(pi/6) - sin(pi/6) * cos(1051*pi/6),
{
have : sin(175*pi) = sin((1051*pi/6) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi) = sin(175*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4*pi) (89),
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


lemma Trigo_729_test (h0 : cos(-pi)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (tan(-2*pi)*tan(-pi)+1)≠ 0) (h3 : (1+tan(-pi)*tan((-2)*pi))≠ 0) (h4 : (sin(-pi)*tan(-2*pi)/cos(-pi)+1)≠ 0) (h5 : (tan((-2)*pi)*(sin(-pi)/cos(-pi))+1)≠ 0) (h6 : cos(-pi)≠ 0) : (-tan(-2*pi) + sin(-pi)/cos(-pi))/(sin(-pi)*tan(-2*pi)/cos(-pi) + 1)=0:=
begin
have : (-tan((-2) * pi) + sin(-pi) / cos(-pi)) / (tan((-2) * pi) * (sin(-pi) / cos(-pi)) + 1) = (-tan(-2*pi) + sin(-pi)/cos(-pi))/(sin(-pi)*tan(-2*pi)/cos(-pi) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = sin(-pi) / cos(-pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (tan(-pi) - tan((-2) * pi)) / (1 + tan(-pi) * tan((-2) * pi)) = (-tan(-2*pi) + tan(-pi))/(tan(-2*pi)*tan(-pi) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(-pi) - tan(-2*pi) ) / ( 1 + tan(-pi) * tan(-2*pi) ),
{
have : tan(pi) = tan((-pi) - (-2*pi)),
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


lemma Trigo_730_test : -sin(389*pi/4)**2 + cos(389*pi/4)**2=- cos(343*pi/2):=
begin
have : cos(389*pi/2) = -sin(389*pi/4) ** 2 + cos(389*pi/4) ** 2,
{
have : cos(389*pi/2) = cos(2*(389*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = cos(389*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = - cos(343*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_731_test : sin(pi/3)*cos(596*pi/3) + cos(-pi/6)*cos(pi/3)=cos(133*pi/2):=
begin
have : cos(596 * pi / 3) * sin(pi / 3) + cos(-pi / 6) * cos(pi / 3) = sin(pi/3)*cos(596*pi/3) + cos(-pi/6)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(596*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/2) = cos(133*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_732_test : sin(2*pi) - sin(pi/3)=(2 - 4*sin(7*pi/12)**2)*sin(5*pi/6):=
begin
have : 2 * (-1 + 2 * (1 - sin(7 * pi / 12) ** 2)) * sin(5 * pi / 6) = (2 - 4*sin(7*pi/12)**2)*sin(5*pi/6),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/12) ** 2 = 1 - sin(7*pi/12) ** 2,
{
rw cos_sq',
},
conv {to_rhs, rw ← this,},
have : 2 * sin(5 * pi / 6) * (2 * cos(7 * pi / 12) ** 2 - 1) = 2*(-1 + 2*cos(7*pi/12)**2)*sin(5*pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(7*pi/6) = 2 * cos(7*pi/12) ** 2 - 1,
{
have : cos(7*pi/6) = cos(2*(7*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) - sin(pi/3) = 2 * sin(5*pi/6) * cos(7*pi/6),
{
rw sin_sub_sin,
have : cos(((2*pi) + (pi/3))/2) = cos(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*pi) - (pi/3))/2) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_733_test : sin(377*pi/2)=-1 + 2*cos(2*pi)**2:=
begin
have : -(1 - cos(2 * pi) ** 2) + cos(2 * pi) ** 2 = -1 + 2*cos(2*pi)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) ** 2 = 1 - cos(2*pi) ** 2,
{
rw sin_sq,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi) = sin(377*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_734_test (h0 : sin(pi/2)≠ 0) : -sin(pi/4)**2 + sin(151*pi/4)**2=sin(pi) / ( 2 * sin(pi/2) ):=
begin
have : -sin(pi / 4) ** 2 + (-sin(151 * pi / 4)) ** 2 = -sin(pi/4)**2 + sin(151*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(151*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_735_test : -1 + 2*sin(1575*pi/8)**2=- sqrt( 2 ) / 2:=
begin
have : cos(3*pi/8) = sin(1575*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*pi/8) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_736_test : -cos(131*pi)=-sin(63*pi/2):=
begin
have : sin(309*pi/2) = -sin(63*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (309*pi/2) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = -cos(131*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(309*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_737_test : -(-sin(pi/2)**2 + cos(pi/2)**2)*sin(196*pi/3)=cos(5*pi/6) / 2 + cos(7*pi/6) / 2:=
begin
have : -sin(196 * pi / 3) * (-sin(pi / 2) * sin(pi / 2) + cos(pi / 2) * cos(pi / 2)) = -(-sin(pi/2)**2 + cos(pi/2)**2)*sin(196*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(pi/2) * sin(pi/2) + cos(pi/2) * cos(pi/2),
{
have : cos(pi) = cos((pi/2) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * -sin(196 * pi / 3) = -sin(196*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(196*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * cos(pi/6) = cos(5*pi/6) / 2 + cos(7*pi/6) / 2,
{
rw cos_mul_cos,
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


lemma Trigo_738_test : -sin(1103*pi/6)=1 - 2*sin(pi/6)**2:=
begin
have : -sin(pi / 6) ** 2 + (1 - sin(pi / 6) ** 2) = 1 - 2*sin(pi/6)**2,
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
have : cos(pi/3) = -sin(1103*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (91),
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


lemma Trigo_739_test : cos(-pi/6)=cos(205*pi/3)*cos(269*pi/2) - sin(205*pi/3)*cos(pi):=
begin
have : - -cos(269 * pi / 2) * cos(205 * pi / 3) - sin(205 * pi / 3) * cos(pi) = cos(205*pi/3)*cos(269*pi/2) - sin(205*pi/3)*cos(pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = -cos(269*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -(sin(205 * pi / 3) * cos(pi) + sin(pi) * cos(205 * pi / 3)) = -sin(pi)*cos(205*pi/3) - sin(205*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(208*pi/3) = sin(205*pi/3) * cos(pi) + sin(pi) * cos(205*pi/3),
{
have : sin(208*pi/3) = sin((205*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(208*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_740_test : sin(-2*pi) * sin(pi/3)=-sin(-7*pi/6)**2 - cos(547*pi/3)/2 + 1/2:=
begin
have : -sin((-7) * pi / 6) ** 2 - cos(547 * pi / 3) / 2 + 1 / 2 = -sin(-7*pi/6)**2 - cos(547*pi/3)/2 + 1/2,
{
field_simp at *,
},
have : cos(-5*pi/3) = cos(547*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-5*pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (1 - 2 * sin((-7) * pi / 6) ** 2) / 2 - cos((-5) * pi / 3) / 2 = -sin(-7*pi/6)**2 - cos(-5*pi/3)/2 + 1/2,
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
have : sin(-2*pi) * sin(pi/3) = cos(-7*pi/3) / 2 - cos(-5*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((-2*pi) + (pi/3)) = cos(-5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*pi) - (pi/3)) = cos(-7*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_741_test : sin(809*pi/6) + sin(pi/3)=-2*sin(pi/4)*sin(1145*pi/12):=
begin
have : sin(pi / 3) + sin(809 * pi / 6) = sin(809*pi/6) + sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(809*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 4) * -sin(1145 * pi / 12) = -2*sin(pi/4)*sin(1145*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/12) = -sin(1145*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) + sin(pi/6) = 2 * sin(pi/4) * cos(pi/12),
{
rw sin_add_sin,
have : sin(((pi/3) + (pi/6))/2) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/3) - (pi/6))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_742_test (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) (h2 : (2*cos(pi/3)**2)≠ 0) : -sin(2*pi/3)**2/(2*cos(pi/3)**2) + 1=- 1 / 2:=
begin
have : 1 - 2 * (sin(2 * pi / 3) / (2 * cos(pi / 3))) ** 2 = -sin(2*pi/3)**2/(2*cos(pi/3)**2) + 1,
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


lemma Trigo_743_test : cos(155*pi)=sin(463*pi/2):=
begin
have : cos(-pi) = cos(155*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(271*pi/2) = sin(463*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (271*pi/2) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = sin(271*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_744_test : -sin(369*pi/2)*cos(373*pi/2)=cos(pi/2) / 2 + cos(3*pi/2) / 2:=
begin
have : cos(pi) = -sin(369*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(373*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) * cos(pi/2) = cos(pi/2) / 2 + cos(3*pi/2) / 2,
{
rw cos_mul_cos,
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


lemma Trigo_745_test (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/2)≠ 0) (h2 : (1+tan(-pi/6)*tan(-pi/2))≠ 0) (h3 : (1+tan(-pi/2)*tan(-pi/6))≠ 0) (h4 : cos(pi/3)≠ 0) (h5 : (2*cos(pi/3))≠ 0) (h6 : (2*cos(pi/3)**2)≠ 0) (h7 : cos(pi/3)≠ 0) : sin(2*pi/3)/(2*cos(pi/3)**2)=(tan(-pi/6) - tan(-pi/2))/(1 + tan(-pi/2)*tan(-pi/6)):=
begin
have : sin(2 * pi / 3) / (2 * cos(pi / 3)) / cos(pi / 3) = sin(2*pi/3)/(2*cos(pi/3)**2),
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
have : (tan(-pi / 6) - tan(-pi / 2)) / (1 + tan(-pi / 6) * tan(-pi / 2)) = (tan(-pi/6) - tan(-pi/2))/(1 + tan(-pi/2)*tan(-pi/6)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_746_test : -sin(30*pi)=1 - 2*cos(273*pi/4)**2:=
begin
have : -(2 * cos(273 * pi / 4) ** 2 - 1) = 1 - 2*cos(273*pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(273*pi/2) = 2 * cos(273*pi/4) ** 2 - 1,
{
have : cos(273*pi/2) = cos(2*(273*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(pi/2) = -sin(30*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = - cos(273*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/2) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_747_test : -sin(5*pi)=-6*cos(-pi/12)**2 + 4*(-1 + 2*cos(-pi/12)**2)**3 + 3:=
begin
have : 4 * (2 * cos(-pi / 12) ** 2 - 1) ** 3 - 3 * (2 * cos(-pi / 12) ** 2 - 1) = -6*cos(-pi/12)**2 + 4*(-1 + 2*cos(-pi/12)**2)**3 + 3,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -sin(5*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (2),
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


lemma Trigo_748_test (h0 : tan(31*pi/4)≠ 0) (h1 : cos((31*pi/2)/2)≠ 0) (h2 : (sin(31*pi/2)/(1+cos(31*pi/2)))≠ 0) (h3 : (1+cos(31*pi/2))≠ 0) (h4 : sin(31*pi/2)≠ 0) : -(cos(31*pi/2) + 1)/sin(31*pi/2)=1:=
begin
have : (-1) / (sin(31 * pi / 2) / (1 + cos(31 * pi / 2))) = -(cos(31*pi/2) + 1)/sin(31*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(31*pi/4) = sin(31*pi/2) / ( 1 + cos(31*pi/2) ),
{
have : tan(31*pi/4) = tan((31*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(31 * pi / 4) = -1/tan(31*pi/4),
{
field_simp at *,
},
have : tan(pi/4) = -1 / tan(31*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (7),
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


lemma Trigo_749_test : -sin(pi)*cos(5*pi/3) + (cos(-2*pi)*cos(3*pi) - sin(-2*pi)*sin(3*pi))*sin(5*pi/3)=sqrt( 3 ) / 2:=
begin
have : -sin(pi) * cos(5 * pi / 3) + sin(5 * pi / 3) * (-sin(3 * pi) * sin((-2) * pi) + cos(3 * pi) * cos((-2) * pi)) = -sin(pi)*cos(5*pi/3) + (cos(-2*pi)*cos(3*pi) - sin(-2*pi)*sin(3*pi))*sin(5*pi/3),
{
field_simp at *,
ring,
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
have : sin(5 * pi / 3) * cos(pi) - sin(pi) * cos(5 * pi / 3) = -sin(pi)*cos(5*pi/3) + sin(5*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(5*pi/3) * cos(pi) - sin(pi) * cos(5*pi/3),
{
have : sin(2*pi/3) = sin((5*pi/3) - (pi)),
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


lemma Trigo_750_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) (h2 : cos(pi/3)≠ 0) (h3 : (2*cos(pi/3))≠ 0) (h4 : (4*sin(pi/6)*cos(pi/3))≠ 0) : sin(2*pi/3)/(4*sin(pi/6)*cos(pi/3))=- cos(809*pi/6):=
begin
have : sin(2 * pi / 3) / (2 * cos(pi / 3)) / (2 * sin(pi / 6)) = sin(2*pi/3)/(4*sin(pi/6)*cos(pi/3)),
{
field_simp at *,
repeat {left},
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
have : cos(pi/6) = - cos(809*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_751_test : 1 - 2*sin(1027*pi/6)**2=2 * cos(pi/6) ** 2 - 1:=
begin
have : 1 - 2 * (-sin(1027 * pi / 6)) ** 2 = 1 - 2*sin(1027*pi/6)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(1027*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (85),
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


lemma Trigo_752_test : -sin(37*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(1223*pi/12) = sin(37*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (1223*pi/12) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(1223*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (51),
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


lemma Trigo_753_test : (-1 + 2*sin(554*pi/3)**2)*cos(-pi)=cos(-2*pi/3) / 2 + cos(-4*pi/3) / 2:=
begin
have : cos(-pi/6) = sin(554*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * (2 * cos(-pi / 6) ** 2 - 1) = (-1 + 2*cos(-pi/6)**2)*cos(-pi),
{
field_simp at *,
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


lemma Trigo_754_test : (1 - 2*sin(15*pi/2)**2)*sin(-pi/3)=sin(-4*pi/3) / 2 + sin(2*pi/3) / 2:=
begin
have : sin(-pi / 3) * (1 - 2 * sin(15 * pi / 2) ** 2) = (1 - 2*sin(15*pi/2)**2)*sin(-pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(15*pi) = 1 - 2 * sin(15*pi/2) ** 2,
{
have : cos(15*pi) = cos(2*(15*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(15*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) * cos(pi) = sin(-4*pi/3) / 2 + sin(2*pi/3) / 2,
{
rw sin_mul_cos,
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
},
rw this,
end


lemma Trigo_755_test (h0 : tan(65*pi/2)≠ 0) (h1 : cos(65*pi/4)≠ 0) (h2 : (2*tan(65*pi/4))≠ 0) (h3 : (2*tan(65*pi/4)/(1-tan(65*pi/4)**2))≠ 0) (h4 : (1-tan(65*pi/4)**2)≠ 0) : -(1 - tan(65*pi/4)**2)/(2*tan(65*pi/4))=- tan(72*pi):=
begin
have : (-1) / (2 * tan(65 * pi / 4) / (1 - tan(65 * pi / 4) ** 2)) = -(1 - tan(65*pi/4)**2)/(2*tan(65*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(65*pi/2) = 2 * tan(65*pi/4) / ( 1 - tan(65*pi/4) ** 2 ),
{
have : tan(65*pi/2) = tan(2*(65*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(65 * pi / 2) = -1/tan(65*pi/2),
{
field_simp at *,
},
have : tan(-pi) = -1 / tan(65*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = - tan(72*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_756_test : cos(259*pi)=sin(179*pi/2):=
begin
have : sin(315*pi/2) = cos(259*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (315*pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(315*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(179*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_757_test : -4*cos(167*pi/2)**3 + 3*cos(167*pi/2)=sin(pi) * cos(-2*pi) - sin(-2*pi) * cos(pi):=
begin
have : (-4) * cos(167 * pi / 2) ** 3 + 3 * cos(167 * pi / 2) = -4*cos(167*pi/2)**3 + 3*cos(167*pi/2),
{
field_simp at *,
},
have : sin(pi) = cos(167*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(pi) ** 3 + 3 * sin(pi) = -4*sin(pi)**3 + 3*sin(pi),
{
field_simp at *,
},
have : sin(3*pi) = -4 * sin(pi) ** 3 + 3 * sin(pi),
{
have : sin(3*pi) = sin(3*(pi)),
{
apply congr_arg,
ring,
},
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) = sin(pi) * cos(-2*pi) - sin(-2*pi) * cos(pi),
{
have : sin(3*pi) = sin((pi) - (-2*pi)),
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


lemma Trigo_758_test : cos(377*pi/3)=-cos(626*pi/3):=
begin
have : cos(-pi/3) = cos(377*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(823*pi/6) = cos(626*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (823*pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(823*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_759_test (h0 : sin(749*pi/4)≠ 0) (h1 : (2*sin(749*pi/4))≠ 0) : -sin(749*pi/2)/(2*sin(749*pi/4))=sqrt( 2 ) / 2:=
begin
have : -(sin(749 * pi / 2) / (2 * sin(749 * pi / 4))) = -sin(749*pi/2)/(2*sin(749*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(749*pi/4) = sin(749*pi/2) / ( 2 * sin(749*pi/4) ),
{
have : sin(749*pi/2) = sin(2*(749*pi/4)),
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
have : sin(pi/4) = -cos(749*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (93),
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


lemma Trigo_760_test (h0 : tan(695*pi/6)≠ 0) : 1/tan(695*pi/6)=- sqrt( 3 ):=
begin
have : -((-1) / tan(695 * pi / 6)) = 1/tan(695*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(127*pi/3) = -1 / tan(695*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (127*pi/3) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(127*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (43),
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


lemma Trigo_761_test : cos(196*pi/3)=sin(-pi/2)*sin(505*pi/6) + sin(-pi/3)*cos(-pi/2):=
begin
have : sin(-5*pi/6) = cos(196*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-5*pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(505*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/6) = sin(-pi/2) * cos(-pi/3) + sin(-pi/3) * cos(-pi/2),
{
have : sin(-5*pi/6) = sin((-pi/2) + (-pi/3)),
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


lemma Trigo_762_test : sin(-pi/2)=-sin(-119*pi/2):=
begin
have : -sin((-119) * pi / 2) = -sin(-119*pi/2),
{
field_simp at *,
},
have : cos(227*pi) = -sin(-119*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (227*pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(73*pi) = cos(227*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (73*pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = cos(73*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_763_test : -sin(386*pi/3)/2 - sin(383*pi/3)/2=- sin(-pi/3) / 2 + sin(-2*pi/3) / 2:=
begin
have : -(sin(386 * pi / 3) / 2 + sin(383 * pi / 3) / 2) = -sin(386*pi/3)/2 - sin(383*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(769*pi/6) * cos(-pi/2) = sin(386*pi/3) / 2 + sin(383*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((769*pi/6) + (-pi/2)) = sin(383*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((769*pi/6) - (-pi/2)) = sin(386*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(769*pi/6) * cos(-pi/2)) = -sin(769*pi/6)*cos(-pi/2),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(-pi/6) = -sin(769*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(-pi/2) = - sin(-pi/3) / 2 + sin(-2*pi/3) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (-pi/6)) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (-pi/6)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_764_test : -cos(0) + cos(81*pi)=2 * sin(-pi/2) * cos(0):=
begin
have : sin(-pi/2) = cos(81*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) - cos(0) = -cos(0) + sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(0),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (0),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_765_test : -sin(pi/24)**2 + cos(3817*pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -sin(pi / 24) ** 2 + (-cos(3817 * pi / 24)) ** 2 = -sin(pi/24)**2 + cos(3817*pi/24)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -cos(3817*pi/24),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/24) (79),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_766_test : cos(157*pi/2)**2=1 / 2 - cos(4*pi) / 2:=
begin
have : cos(227*pi/2) = cos(157*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (227*pi/2) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(227 * pi / 2)) ** 2 = cos(227*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -cos(227*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_767_test : -sin(1509*pi/8)**2 + cos(3*pi/8)**2=- sqrt( 2 ) / 2:=
begin
have : sin(3*pi/8) = sin(1509*pi/8),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/8) (94),
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


lemma Trigo_768_test : -sin(293*pi/2)=cos(179*pi):=
begin
have : cos(-pi) = -sin(293*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos(179 * pi) = cos(179*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(333*pi/2) = -cos(179*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (333*pi/2) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = - sin(333*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_769_test : (-sin(-4*pi/3)*sin(pi/2) + cos(-4*pi/3)*cos(pi/2))*cos(-pi/2) + sin(-5*pi/6)*sin(-pi/2)=sin(329*pi/6):=
begin
have : (-sin((-4) * pi / 3) * sin(pi / 2) + cos((-4) * pi / 3) * cos(pi / 2)) * cos(-pi / 2) + sin((-5) * pi / 6) * sin(-pi / 2) = (-sin(-4*pi/3)*sin(pi/2) + cos(-4*pi/3)*cos(pi/2))*cos(-pi/2) + sin(-5*pi/6)*sin(-pi/2),
{
field_simp at *,
},
have : cos(-5*pi/6) = -sin(-4*pi/3) * sin(pi/2) + cos(-4*pi/3) * cos(pi/2),
{
have : cos(-5*pi/6) = cos((-4*pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 6) * sin(-pi / 2) + cos((-5) * pi / 6) * cos(-pi / 2) = cos(-5*pi/6)*cos(-pi/2) + sin(-5*pi/6)*sin(-pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(-5*pi/6) * sin(-pi/2) + cos(-5*pi/6) * cos(-pi/2),
{
have : cos(-pi/3) = cos((-5*pi/6) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = sin(329*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_770_test : -cos(209*pi)=1 - 2 * sin(-2*pi) ** 2:=
begin
have : sin(203*pi/2) = cos(209*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (203*pi/2) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-4*pi) = -sin(203*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-4*pi) (48),
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


lemma Trigo_771_test (h0 : cos(-2*pi)≠ 0) (h1 : (2*cos(4*pi))≠ 0) : -sin(58*pi)=sin(-4*pi)/(2*cos(4*pi)):=
begin
have : sin(-2*pi) = -sin(58*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2*pi) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-4) * pi) / (2 * cos(4 * pi)) = sin(-4*pi)/(2*cos(4*pi)),
{
field_simp at *,
},
have : cos(-2*pi) = cos(4*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi) (3),
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


lemma Trigo_772_test : sin(1309*pi/6)=cos(403*pi/3):=
begin
have : cos(491*pi/3) = sin(1309*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (491*pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(491*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(403*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_773_test : sin(-2*pi)*cos(50*pi/3) + sin(50*pi/3)*cos(-2*pi)=sqrt( 3 ) / 2:=
begin
have : sin(50 * pi / 3) * cos((-2) * pi) + sin((-2) * pi) * cos(50 * pi / 3) = sin(-2*pi)*cos(50*pi/3) + sin(50*pi/3)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(44*pi/3) = sin(50*pi/3) * cos(-2*pi) + sin(-2*pi) * cos(50*pi/3),
{
have : sin(44*pi/3) = sin((50*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(44*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (7),
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


lemma Trigo_774_test : -sin(3*pi/8)**2 + (sin(-pi/6)*sin(5*pi/24) + cos(-pi/6)*cos(5*pi/24))**2=- sqrt( 2 ) / 2:=
begin
have : -sin(3 * pi / 8) ** 2 + (sin(5 * pi / 24) * sin(-pi / 6) + cos(5 * pi / 24) * cos(-pi / 6)) ** 2 = -sin(3*pi/8)**2 + (sin(-pi/6)*sin(5*pi/24) + cos(-pi/6)*cos(5*pi/24))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = sin(5*pi/24) * sin(-pi/6) + cos(5*pi/24) * cos(-pi/6),
{
have : cos(3*pi/8) = cos((5*pi/24) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_775_test : cos(229*pi/6)=-sin(-223*pi/3):=
begin
have : cos(-pi/6) = cos(229*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-223) * pi / 3) = -sin(-223*pi/3),
{
field_simp at *,
},
have : sin(511*pi/3) = -sin(-223*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (511*pi/3) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = sin(511*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_776_test : -sin(2*pi)*cos(3*pi) + sin(5*pi)/2 - sin(-pi)/2=0:=
begin
have : -sin(2 * pi) * cos(3 * pi) + (-sin(-pi) / 2 + sin(5 * pi) / 2) = -sin(2*pi)*cos(3*pi) + sin(5*pi)/2 - sin(-pi)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi) * cos(2*pi) = -sin(-pi) / 2 + sin(5*pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((2*pi) + (3*pi)) = sin(5*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (3*pi)) = sin(-pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(3*pi) * cos(2*pi)) = sin(3*pi)*cos(2*pi),
{
ring,
},
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


lemma Trigo_777_test : 2*sin(-7*pi/6)*cos(-7*pi/6)*cos(pi/3) + sin(pi/3)*cos(-7*pi/3)=- sin(75*pi):=
begin
have : 2 * sin((-7) * pi / 6) * cos((-7) * pi / 6) * cos(pi / 3) + sin(pi / 3) * cos((-7) * pi / 3) = 2*sin(-7*pi/6)*cos(-7*pi/6)*cos(pi/3) + sin(pi/3)*cos(-7*pi/3),
{
field_simp at *,
},
have : sin(-7*pi/3) = 2 * sin(-7*pi/6) * cos(-7*pi/6),
{
have : sin(-7*pi/3) = sin(2*(-7*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin((-7) * pi / 3) * cos(pi / 3) + sin(pi / 3) * cos((-7) * pi / 3) = sin(-7*pi/3)*cos(pi/3) + sin(pi/3)*cos(-7*pi/3),
{
field_simp at *,
},
have : sin(-2*pi) = sin(-7*pi/3) * cos(pi/3) + sin(pi/3) * cos(-7*pi/3),
{
have : sin(-2*pi) = sin((-7*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = - sin(75*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_778_test : -cos(2963*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(1799*pi/12) = -cos(2963*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (1799*pi/12) (48),
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


lemma Trigo_779_test : -sin(312*pi) - sin(-pi/6)=2 * sin(-11*pi/12) * cos(-13*pi/12):=
begin
have : sin(165*pi) = -sin(312*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (165*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(165*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) - sin(-pi/6) = 2 * sin(-11*pi/12) * cos(-13*pi/12),
{
rw sin_sub_sin,
have : cos(((-2*pi) + (-pi/6))/2) = cos(-13*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-2*pi) - (-pi/6))/2) = sin(-11*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_780_test (h0 : cos(pi)≠ 0) (h1 : (2*cos(pi))≠ 0) (h2 : (2*cos(60*pi))≠ 0) (h3 : (2*-cos(60*pi))≠ 0) : -sin(2*pi)*cos(-pi/6)/(2*cos(60*pi))=sin(7*pi/6) / 2 + sin(5*pi/6) / 2:=
begin
have : sin(2 * pi) * cos(-pi / 6) / (2 * -cos(60 * pi)) = -sin(2*pi)*cos(-pi/6)/(2*cos(60*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -cos(60*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) / (2 * cos(pi)) * cos(-pi / 6) = sin(2*pi)*cos(-pi/6)/(2*cos(pi)),
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
have : sin(pi) * cos(-pi/6) = sin(7*pi/6) / 2 + sin(5*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi) + (-pi/6)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi) - (-pi/6)) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_781_test : sin(9*pi/2)=-1 + 2*sin(153*pi/2)**2:=
begin
have : -(1 - 2 * sin(153 * pi / 2) ** 2) = -1 + 2*sin(153*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(153*pi) = 1 - 2 * sin(153*pi/2) ** 2,
{
have : cos(153*pi) = cos(2*(153*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(9*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = - cos(153*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_782_test : cos(-pi/2)=-2*sin(6*pi)*cos(6*pi):=
begin
have : -(2 * sin(6 * pi) * cos(6 * pi)) = -2*sin(6*pi)*cos(6*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(12*pi) = 2 * sin(6*pi) * cos(6*pi),
{
have : sin(12*pi) = sin(2*(6*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : sin(124*pi) = -sin(12*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (124*pi) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = sin(124*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/2) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_783_test : -8*sin(-pi/2)**2*cos(-pi/2)**2 + 1=sin(257*pi/2):=
begin
have : 1 - 2 * (2 * sin(-pi / 2) * cos(-pi / 2)) ** 2 = -8*sin(-pi/2)**2*cos(-pi/2)**2 + 1,
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
have : cos(-2*pi) = sin(257*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_784_test : sin(-161*pi/3)=sqrt( 3 ) / 2:=
begin
have : - -sin((-161) * pi / 3) = sin(-161*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(355*pi/6) = -sin(-161*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (355*pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(355*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (29),
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


lemma Trigo_785_test (h0 : cos(73*pi/12)≠ 0) (h1 : (2*cos(73*pi/12))≠ 0) : sin(73*pi/6)/(2*cos(73*pi/12))=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(73*pi/12) = sin(73*pi/6) / ( 2 * cos(73*pi/12) ),
{
have : sin(73*pi/6) = sin(2*(73*pi/12)),
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
have : sin(pi/12) = sin(73*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (3),
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


lemma Trigo_786_test : sin(-267*pi/2)=2 * cos(pi) ** 2 - 1:=
begin
have : sin((-267) * pi / 2) = sin(-267*pi/2),
{
field_simp at *,
},
have : cos(168*pi) = sin(-267*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (168*pi) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = cos(168*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (83),
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


lemma Trigo_787_test (h0 : cos(3*pi)≠ 0) (h1 : cos(2*pi)≠ 0) (h2 : (1+tan(3*pi)*tan(2*pi))≠ 0) (h3 : (tan(2*pi)*tan(3*pi)+1)≠ 0) (h4 : (-tan(82*pi)*tan(3*pi)+1)≠ 0) (h5 : (-tan(3*pi)*tan(82*pi)+1)≠ 0) : (tan(82*pi) + tan(3*pi))/(-tan(3*pi)*tan(82*pi) + 1)=1 / tan(67*pi/2):=
begin
have : (- -tan(82 * pi) + tan(3 * pi)) / (-tan(82 * pi) * tan(3 * pi) + 1) = (tan(82*pi) + tan(3*pi))/(-tan(3*pi)*tan(82*pi) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = -tan(82*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(3 * pi) - tan(2 * pi)) / (1 + tan(3 * pi) * tan(2 * pi)) = (-tan(2*pi) + tan(3*pi))/(tan(2*pi)*tan(3*pi) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi) = ( tan(3*pi) - tan(2*pi) ) / ( 1 + tan(3*pi) * tan(2*pi) ),
{
have : tan(pi) = tan((3*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi) = 1 / tan(67*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_788_test : sin(pi/6)=-sin(299*pi/6):=
begin
have : cos(107*pi/3) = -sin(299*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (107*pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(17*pi/3) = cos(107*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (17*pi/3) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = cos(17*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_789_test : 2*sin(130*pi/3)*cos(130*pi/3)=- sin(353*pi/3):=
begin
have : sin(260*pi/3) = 2 * sin(130*pi/3) * cos(130*pi/3),
{
have : sin(260*pi/3) = sin(2*(130*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(260*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - sin(353*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_790_test : -cos(1049*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(53*pi/3) = cos(1049*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (53*pi/3) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(53*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (8),
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


lemma Trigo_791_test : 2*sin(pi/2)*cos(225*pi/2)=0:=
begin
have : cos(pi/2) = cos(225*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (56),
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_792_test : (-sin(1139*pi/6)**2 + cos(pi/6)**2)**2=cos(2*pi/3) / 2 + 1 / 2:=
begin
have : (-(-sin(1139 * pi / 6)) ** 2 + cos(pi / 6) ** 2) ** 2 = (-sin(1139*pi/6)**2 + cos(pi/6)**2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(1139*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi / 6) * sin(pi / 6) + cos(pi / 6) * cos(pi / 6)) ** 2 = (-sin(pi/6)**2 + cos(pi/6)**2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(pi/6) * sin(pi/6) + cos(pi/6) * cos(pi/6),
{
have : cos(pi/3) = cos((pi/6) + (pi/6)),
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


lemma Trigo_793_test : cos(101*pi)=sin(327*pi/2):=
begin
have : - -cos(101 * pi) = cos(101*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(42*pi) = -cos(101*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (42*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -cos(42*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(327*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_794_test (h0 : sin(3*pi/8)≠ 0) (h1 : (2*sin(3*pi/8)**2)≠ 0) (h2 : (2*sin(3*pi/8))≠ 0) : -1 + sin(3*pi/4)**2/(2*sin(3*pi/8)**2)=- sqrt( 2 ) / 2:=
begin
have : -1 + 2 * (sin(3 * pi / 4) / (2 * sin(3 * pi / 8))) ** 2 = -1 + sin(3*pi/4)**2/(2*sin(3*pi/8)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/8) = sin(3*pi/4) / ( 2 * sin(3*pi/8) ),
{
have : sin(3*pi/4) = sin(2*(3*pi/8)),
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


lemma Trigo_795_test : -sin(359*pi/3)=sqrt( 3 ) / 2:=
begin
have : sin(107*pi/3) = sin(359*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (107*pi/3) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(107*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (17),
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


lemma Trigo_796_test : -2*sin(pi/2)**2 - sin(34*pi) + 1=2 * cos(pi/4) * cos(3*pi/4):=
begin
have : (-2) * sin(pi / 2) ** 2 + -sin(34 * pi) + 1 = -2*sin(pi/2)**2 - sin(34*pi) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(34*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * sin(pi / 2) ** 2 + cos(pi / 2) = -2*sin(pi/2)**2 + cos(pi/2) + 1,
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
have : cos(pi) + cos(pi/2) = 2 * cos(pi/4) * cos(3*pi/4),
{
rw cos_add_cos,
have : cos(((pi) + (pi/2))/2) = cos(3*pi/4),
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
ring,
},
rw this,
end


lemma Trigo_797_test : -sin(279*pi/2)=1:=
begin
have : cos(29*pi) = sin(279*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (29*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(29*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (14),
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


lemma Trigo_798_test (h0 : tan(1097*pi/12)≠ 0) (h1 : tan(1637*pi/12)≠ 0) : 1/tan(1637*pi/12)=2 - sqrt( 3 ):=
begin
have : tan(1097*pi/12) = tan(1637*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (1097*pi/12) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 1 / tan(1097*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (91),
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


lemma Trigo_799_test : -1 + 2*(1 - 2*sin(pi/4)**2)**2=- 1:=
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


lemma Trigo_800_test : sin(1085*pi/6)=-cos(-238*pi/3):=
begin
have : cos(pi/3) = sin(1085*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos((-238) * pi / 3) = -cos(-238*pi/3),
{
field_simp at *,
},
have : sin(905*pi/6) = -cos(-238*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (905*pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = sin(905*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_801_test : cos(0)=-(1 - 2*sin(pi/6)**2)*sin(743*pi/6) - sin(-pi/3)*sin(pi/3):=
begin
have : -sin(743 * pi / 6) * (1 - 2 * sin(pi / 6) ** 2) - sin(-pi / 3) * sin(pi / 3) = -(1 - 2*sin(pi/6)**2)*sin(743*pi/6) - sin(-pi/3)*sin(pi/3),
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
have : -sin(-pi / 3) * sin(pi / 3) + -sin(743 * pi / 6) * cos(pi / 3) = -sin(743*pi/6)*cos(pi/3) - sin(-pi/3)*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -sin(743*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(0) = - sin(-pi/3) * sin(pi/3) + cos(-pi/3) * cos(pi/3),
{
have : cos(0) = cos((-pi/3) + (pi/3)),
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


lemma Trigo_802_test : -3 + 6*sin(pi/12)**2 + 4*(1 - 2*sin(pi/12)**2)**3=cos(349*pi/2):=
begin
have : (-3) * (1 - 2 * sin(pi / 12) ** 2) + 4 * (1 - 2 * sin(pi / 12) ** 2) ** 3 = -3 + 6*sin(pi/12)**2 + 4*(1 - 2*sin(pi/12)**2)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/2) = cos(349*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_803_test (h0 : cos(-3*pi/2)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (1+tan(-2*pi)*tan(-3*pi/2))≠ 0) (h3 : (1+tan((-3)*pi/2)*tan((-2)*pi))≠ 0) (h4 : cos(-3*pi/2)≠ 0) (h5 : cos(-2*pi)≠ 0) (h6 : tan((-3*pi/2)+(-2*pi))≠ 0) (h7 : 1-tan(-3*pi/2)*tan(-2*pi)≠ 0) (h8 : tan((-7)*pi/2)≠ 0) (h9 : tan(-7*pi/2)≠ 0) (h10 : (1+(-(tan((-3)*pi/2)+tan((-2)*pi))/tan((-7)*pi/2)+1))≠ 0) (h11 : ((-tan(-3*pi/2)-tan(-2*pi))/tan(-7*pi/2)+2)≠ 0) : (-tan(-2*pi) + tan(-3*pi/2))/((-tan(-3*pi/2) - tan(-2*pi))/tan(-7*pi/2) + 2)=- tan(163*pi/2):=
begin
have : (-tan((-2) * pi) + tan((-3) * pi / 2)) / (1 + (-(tan((-3) * pi / 2) + tan((-2) * pi)) / tan((-7) * pi / 2) + 1)) = (-tan(-2*pi) + tan(-3*pi/2))/((-tan(-3*pi/2) - tan(-2*pi))/tan(-7*pi/2) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-3*pi/2) * tan(-2*pi) = -( tan(-3*pi/2) + tan(-2*pi) ) / tan(-7*pi/2) + 1,
{
rw tan_mul_tan',
have : tan((-3*pi/2) + (-2*pi)) = tan(-7*pi/2),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-3*pi/2) * tan(-2*pi)) = tan(-2*pi)*tan(-3*pi/2),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan((-3) * pi / 2) - tan((-2) * pi)) / (1 + tan((-3) * pi / 2) * tan((-2) * pi)) = (-tan(-2*pi) + tan(-3*pi/2))/(1 + tan(-2*pi)*tan(-3*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = ( tan(-3*pi/2) - tan(-2*pi) ) / ( 1 + tan(-3*pi/2) * tan(-2*pi) ),
{
have : tan(pi/2) = tan((-3*pi/2) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = - tan(163*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/2) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_804_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : (-4*sin(pi/3)**3 + 3*sin(pi/3))/(2*cos(pi/2))=sin(pi/3) * cos(pi/6) + sin(pi/6) * cos(pi/3):=
begin
have : ((-4) * sin(pi / 3) ** 3 + 3 * sin(pi / 3)) / (2 * cos(pi / 2)) = (-4*sin(pi/3)**3 + 3*sin(pi/3))/(2*cos(pi/2)),
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


lemma Trigo_805_test : sin(55*pi)*sin(349*pi/3)=sin(-pi/6) / 2 + sin(5*pi/6) / 2:=
begin
have : sin(349 * pi / 3) * sin(55 * pi) = sin(55*pi)*sin(349*pi/3),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(55*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(349*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) * cos(pi/2) = sin(-pi/6) / 2 + sin(5*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/3) + (pi/2)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (pi/2)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_806_test : cos(47*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -cos(47 * pi / 4) = cos(47*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(27*pi/4) = -cos(47*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (27*pi/4) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(27*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/4) (3),
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


lemma Trigo_807_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) (h2 : (2*sin(169*pi))≠ 0) (h3 : (2*-sin(169*pi))≠ 0) : -sin(pi)/(2*sin(169*pi))=1:=
begin
have : sin(pi) / (2 * -sin(169 * pi)) = -sin(pi)/(2*sin(169*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(169*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (84),
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_808_test : -cos(146*pi/3)=1 / 2:=
begin
have : sin(13*pi/6) = -cos(146*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (13*pi/6) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(13*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (1),
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


lemma Trigo_809_test (h0 : sin(130*pi)≠ 0) (h1 : (4*sin(130*pi)**2)≠ 0) (h2 : (2*sin(130*pi))≠ 0) : sin(-2*pi) ** 2=1 - sin(260*pi)**2/(4*sin(130*pi)**2):=
begin
have : 1 - (sin(260 * pi) / (2 * sin(130 * pi))) ** 2 = 1 - sin(260*pi)**2/(4*sin(130*pi)**2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(130*pi) = sin(260*pi) / ( 2 * sin(130*pi) ),
{
have : sin(260*pi) = sin(2*(130*pi)),
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
have : cos(-2*pi) = cos(130*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) ** 2 = 1 - cos(-2*pi) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_810_test : sin(95*pi)*cos(-pi/6) - sin(-pi/6)*sin(pi/2)=1 / 2:=
begin
have : cos(-pi / 6) * sin(95 * pi) - sin(-pi / 6) * sin(pi / 2) = sin(95*pi)*cos(-pi/6) - sin(-pi/6)*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = sin(95*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/2) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/3) = 1 / 2,
{
rw cos_pi_div_three,
},
rw this,
end


lemma Trigo_811_test : 2*cos(3*pi/8)*cos(1567*pi/8)=sqrt( 2 ) / 2:=
begin
have : 2 * cos(1567 * pi / 8) * cos(3 * pi / 8) = 2*cos(3*pi/8)*cos(1567*pi/8),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/8) = cos(1567*pi/8),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/8) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_812_test (h0 : cos(36*pi)≠ 0) (h1 : (2*cos(36*pi))≠ 0) : -sin(72*pi)/(2*cos(36*pi))=0:=
begin
have : -(sin(72 * pi) / (2 * cos(36 * pi))) = -sin(72*pi)/(2*cos(36*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(36*pi) = sin(72*pi) / ( 2 * cos(36*pi) ),
{
have : sin(72*pi) = sin(2*(36*pi)),
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
have : cos(pi/2) = -sin(36*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (17),
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


lemma Trigo_813_test : cos(94*pi)=1 - 2*cos(53*pi/2)**2:=
begin
have : cos(-4*pi) = cos(94*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-4*pi) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (-cos(53 * pi / 2)) ** 2 = 1 - 2*cos(53*pi/2)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = -cos(53*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (14),
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


lemma Trigo_814_test : cos(0)=sin(-pi/6)*cos(896*pi/3) + cos(-pi/6)*cos(pi/6):=
begin
have : sin(823*pi/6) = cos(896*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (823*pi/6) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -sin(-pi / 6) * -sin(823 * pi / 6) + cos(-pi / 6) * cos(pi / 6) = sin(-pi/6)*sin(823*pi/6) + cos(-pi/6)*cos(pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = -sin(823*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (68),
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


lemma Trigo_815_test (h0 : cos(pi/12)≠ 0) (h1 : (1-tan(pi/12)**2)≠ 0) (h2 : cos(pi/24)≠ 0) (h3 : ((1-tan(pi/24)**2)*(-4*tan(pi/24)**2/(1-tan(pi/24)**2)**2+1))≠ 0) (h4 : (1-(2*tan(pi/24)/(1-tan(pi/24)**2))**2)≠ 0) (h5 : (1-tan(pi/24)**2)≠ 0) : 4*tan(pi/24)/((1 - tan(pi/24)**2)*(-4*tan(pi/24)**2/(1 - tan(pi/24)**2)**2 + 1))=1 / tan(100*pi/3):=
begin
have : 2 * (2 * tan(pi / 24) / (1 - tan(pi / 24) ** 2)) / (1 - (2 * tan(pi / 24) / (1 - tan(pi / 24) ** 2)) ** 2) = 4*tan(pi/24)/((1 - tan(pi/24)**2)*(-4*tan(pi/24)**2/(1 - tan(pi/24)**2)**2 + 1)),
{
field_simp at *,
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
have : tan(pi/6) = 1 / tan(100*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_816_test : sin(3*pi/2)*cos(pi/2) + cos(3*pi/2)*cos(131*pi)=0:=
begin
have : sin(3 * pi / 2) * cos(pi / 2) - -cos(131 * pi) * cos(3 * pi / 2) = sin(3*pi/2)*cos(pi/2) + cos(3*pi/2)*cos(131*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(131*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (65),
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
have : sin(pi) = 0,
{
rw sin_pi,
},
rw this,
end


lemma Trigo_817_test : sin(3*pi/2)*sin(369*pi/2) + cos(pi/2)*cos(3*pi/2)=- cos(86*pi):=
begin
have : sin(369 * pi / 2) * sin(3 * pi / 2) + cos(pi / 2) * cos(3 * pi / 2) = sin(3*pi/2)*sin(369*pi/2) + cos(pi/2)*cos(3*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(369*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/2) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3 * pi / 2) * sin(pi / 2) + cos(3 * pi / 2) * cos(pi / 2) = sin(pi/2)*sin(3*pi/2) + cos(pi/2)*cos(3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(3*pi/2) * sin(pi/2) + cos(3*pi/2) * cos(pi/2),
{
have : cos(pi) = cos((3*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(86*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_818_test (h0 : cos(pi/2)≠ 0) (h1 : (2*cos(pi/2))≠ 0) : sin(72*pi)/(2*cos(pi/2))=1:=
begin
have : sin(pi) = sin(72*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (36),
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
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_819_test : -3*sin(841*pi/18) + 4*sin(841*pi/18)**3=- cos(311*pi/3):=
begin
have : -((-4) * sin(841 * pi / 18) ** 3 + 3 * sin(841 * pi / 18)) = -3*sin(841*pi/18) + 4*sin(841*pi/18)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(841*pi/6) = -4 * sin(841*pi/18) ** 3 + 3 * sin(841*pi/18),
{
have : sin(841*pi/6) = sin(3*(841*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(841*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = - cos(311*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_820_test (h0 : tan(241*pi/4)≠ 0) (h1 : cos(241*pi/4)≠ 0) (h2 : sin(241*pi/4)≠ 0) (h3 : (sin(241*pi/4)/cos(241*pi/4))≠ 0) : -cos(241*pi/4)/sin(241*pi/4)=- 1:=
begin
have : (-1) / (sin(241 * pi / 4) / cos(241 * pi / 4)) = -cos(241*pi/4)/sin(241*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(241*pi/4) = sin(241*pi/4) / cos(241*pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (-1) / tan(241 * pi / 4) = -1/tan(241*pi/4),
{
field_simp at *,
},
have : tan(3*pi/4) = -1 / tan(241*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (3*pi/4) (59),
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


lemma Trigo_821_test : tan(73*pi/12)=2 - sqrt( 3 ):=
begin
have : - -tan(73 * pi / 12) = tan(73*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(695*pi/12) = -tan(73*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (695*pi/12) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(695*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (58),
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


lemma Trigo_822_test : (-sin(pi/2)*cos(-3*pi/2) + (cos(-3*pi/2)*cos(2*pi) - sin(-3*pi/2)*sin(2*pi))*sin(-3*pi/2))*sin(pi/6)=cos(13*pi/6) / 2 - cos(-11*pi/6) / 2:=
begin
have : (sin((-3) * pi / 2) * (-sin((-3) * pi / 2) * sin(2 * pi) + cos((-3) * pi / 2) * cos(2 * pi)) - sin(pi / 2) * cos((-3) * pi / 2)) * sin(pi / 6) = (-sin(pi/2)*cos(-3*pi/2) + (cos(-3*pi/2)*cos(2*pi) - sin(-3*pi/2)*sin(2*pi))*sin(-3*pi/2))*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(-3*pi/2) * sin(2*pi) + cos(-3*pi/2) * cos(2*pi),
{
have : cos(pi/2) = cos((-3*pi/2) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) * (sin((-3) * pi / 2) * cos(pi / 2) - sin(pi / 2) * cos((-3) * pi / 2)) = (sin(-3*pi/2)*cos(pi/2) - sin(pi/2)*cos(-3*pi/2))*sin(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(-3*pi/2) * cos(pi/2) - sin(pi/2) * cos(-3*pi/2),
{
have : sin(-2*pi) = sin((-3*pi/2) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * sin(-2*pi) = cos(13*pi/6) / 2 - cos(-11*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((pi/6) + (-2*pi)) = cos(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/6) - (-2*pi)) = cos(13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_823_test : sin(2*pi/3)=(-sin(269*pi/3)**2 + cos(269*pi/3)**2)*sin(-pi) + sin(-pi/3)*cos(-pi):=
begin
have : sin(-pi) * (-sin(269 * pi / 3) ** 2 + cos(269 * pi / 3) ** 2) + sin(-pi / 3) * cos(-pi) = (-sin(269*pi/3)**2 + cos(269*pi/3)**2)*sin(-pi) + sin(-pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(538*pi/3) = -sin(269*pi/3) ** 2 + cos(269*pi/3) ** 2,
{
have : cos(538*pi/3) = cos(2*(269*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 3) * cos(-pi) - sin(-pi) * -cos(538 * pi / 3) = sin(-pi)*cos(538*pi/3) + sin(-pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -cos(538*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/3) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
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


lemma Trigo_824_test : sin(211*pi)=0:=
begin
have : sin(59*pi) = sin(211*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (59*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(59*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (29),
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


lemma Trigo_825_test : -sin(-2*pi)*cos(-3*pi/2) + cos(-2*pi)*cos(78*pi)=1:=
begin
have : -sin((-2) * pi) * cos((-3) * pi / 2) + cos(78 * pi) * cos((-2) * pi) = -sin(-2*pi)*cos(-3*pi/2) + cos(-2*pi)*cos(78*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2) = cos(78*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-3*pi/2) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-3) * pi / 2) * cos((-2) * pi) - sin((-2) * pi) * cos((-3) * pi / 2) = -sin(-2*pi)*cos(-3*pi/2) + sin(-3*pi/2)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : sin(pi/2) = 1,
{
rw sin_pi_div_two,
},
rw this,
end


lemma Trigo_826_test : cos(-121*pi)=4 * cos(-pi) ** 3 - 3 * cos(-pi):=
begin
have : - -cos((-121) * pi) = cos(-121*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(289*pi/2) = -cos(-121*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (289*pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi) = -sin(289*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi) (70),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_827_test : sin(455*pi/3)=- sqrt( 3 ) / 2:=
begin
have : - -sin(455 * pi / 3) = sin(455*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(20*pi/3) = -sin(455*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (20*pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(20*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (3),
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


lemma Trigo_828_test : sin(-pi)=-1/2 + cos(331*pi/2)/2 + cos(331*pi/4)**2:=
begin
have : -(1 / 2 - cos(331 * pi / 2) / 2) + cos(331 * pi / 4) ** 2 = -1/2 + cos(331*pi/2)/2 + cos(331*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(331*pi/4) ** 2 = 1 / 2 - cos(331*pi/2) / 2,
{
have : cos(331*pi/2) = cos(2*(331*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_rhs, rw ← this,},
have : cos(331*pi/2) = -sin(331*pi/4) ** 2 + cos(331*pi/4) ** 2,
{
have : cos(331*pi/2) = cos(2*(331*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(331*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_829_test : 1 - 2*cos(1015*pi/12)**2=- cos(595*pi/6):=
begin
have : -(2 * cos(1015 * pi / 12) ** 2 - 1) = 1 - 2*cos(1015*pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1015*pi/6) = 2 * cos(1015*pi/12) ** 2 - 1,
{
have : cos(1015*pi/6) = cos(2*(1015*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -cos(1015*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(595*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_831_test : cos(-2*pi)*cos(17*pi/6) - (-4*sin(17*pi/18)**3 + 3*sin(17*pi/18))*sin(-2*pi)=- sqrt( 3 ) / 2:=
begin
have : cos((-2) * pi) * cos(17 * pi / 6) - sin((-2) * pi) * ((-4) * sin(17 * pi / 18) ** 3 + 3 * sin(17 * pi / 18)) = cos(-2*pi)*cos(17*pi/6) - (-4*sin(17*pi/18)**3 + 3*sin(17*pi/18))*sin(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/6) = -4 * sin(17*pi/18) ** 3 + 3 * sin(17*pi/18),
{
have : sin(17*pi/6) = sin(3*(17*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(17 * pi / 6) * sin((-2) * pi) + cos(17 * pi / 6) * cos((-2) * pi) = cos(-2*pi)*cos(17*pi/6) - sin(-2*pi)*sin(17*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(17*pi/6) * sin(-2*pi) + cos(17*pi/6) * cos(-2*pi),
{
have : cos(5*pi/6) = cos((17*pi/6) + (-2*pi)),
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


lemma Trigo_832_test : (-sin(-pi/12)**2 + cos(-pi/6)/2 + 1/2)*sin(-pi/2)=sin(-pi/3) / 2 + sin(-2*pi/3) / 2:=
begin
have : (-sin(-pi / 12) ** 2 + (cos(-pi / 6) / 2 + 1 / 2)) * sin(-pi / 2) = (-sin(-pi/12)**2 + cos(-pi/6)/2 + 1/2)*sin(-pi/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/12) ** 2 = cos(-pi/6) / 2 + 1 / 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 2) * (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(-pi/2),
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
have : sin(-pi/2) * cos(-pi/6) = sin(-pi/3) / 2 + sin(-2*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((-pi/2) + (-pi/6)) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (-pi/6)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_833_test : (3*sin(46*pi/9) - 4*sin(46*pi/9)**3)**2=1 - cos(pi/3) ** 2:=
begin
have : ((-4) * sin(46 * pi / 9) ** 3 + 3 * sin(46 * pi / 9)) ** 2 = (3*sin(46*pi/9) - 4*sin(46*pi/9)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(46*pi/3) = -4 * sin(46*pi/9) ** 3 + 3 * sin(46*pi/9),
{
have : sin(46*pi/3) = sin(3*(46*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(46 * pi / 3)) ** 2 = sin(46*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(46*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/3) (7),
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


lemma Trigo_834_test : cos(575*pi/3)**2=1/2 - cos(385*pi/3)/2:=
begin
have : (-cos(575 * pi / 3)) ** 2 = cos(575*pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -cos(575*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(385*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (64),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_835_test : -sin(-2*pi)*sin(381*pi/2)=sin(-2*pi)*cos(-pi):=
begin
have : 1 / 2 * (2 * sin((-2) * pi) * cos(-pi)) = sin(-2*pi)*cos(-pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-3*pi) + sin(-pi) = 2 * sin(-2*pi) * cos(-pi),
{
rw sin_add_sin,
have : sin(((-3*pi) + (-pi))/2) = sin(-2*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-3*pi) - (-pi))/2) = cos(-pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 1/2*(sin(-3*pi) + sin(-pi)) = sin(-3*pi)/2+sin(-pi)/2,
{
ring,
},
conv {to_rhs, rw this,},
have : sin((-2) * pi) * -sin(381 * pi / 2) = -sin(-2*pi)*sin(381*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(381*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) * cos(pi) = sin(-3*pi) / 2 + sin(-pi) / 2,
{
rw sin_mul_cos,
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
},
rw this,
end


lemma Trigo_836_test (h0 : sin(38*pi)≠ 0) (h1 : (2*sin(38*pi))≠ 0) : -sin(253*pi/2)=-sin(76*pi)/(2*sin(38*pi)):=
begin
have : sin(-pi/2) = -sin(253*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(76 * pi) / (2 * sin(38 * pi))) = -sin(76*pi)/(2*sin(38*pi)),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(38*pi) = sin(76*pi) / ( 2 * sin(38*pi) ),
{
have : sin(76*pi) = sin(2*(38*pi)),
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
have : sin(-pi/2) = - cos(38*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_837_test (h0 : tan(107*pi/2)≠ 0) (h1 : cos((107*pi)/2)≠ 0) (h2 : (sin(107*pi)/(1+cos(107*pi)))≠ 0) (h3 : (1+cos(107*pi))≠ 0) (h4 : sin(107*pi)≠ 0) : (cos(107*pi) + 1)/sin(107*pi)=1 / tan(129*pi/2):=
begin
have : 1 / (sin(107 * pi) / (1 + cos(107 * pi))) = (cos(107*pi) + 1)/sin(107*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(107*pi/2) = sin(107*pi) / ( 1 + cos(107*pi) ),
{
have : tan(107*pi/2) = tan((107*pi)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = 1 / tan(107*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = 1 / tan(129*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_838_test : -1 + cos(-pi/2) + 2*(sin(11*pi/12)*sin(pi) + cos(11*pi/12)*cos(pi))**2=2 * cos(-pi/6) * cos(-pi/3):=
begin
have : cos(-pi/12) = sin(11*pi/12) * sin(pi) + cos(11*pi/12) * cos(pi),
{
have : cos(-pi/12) = cos((11*pi/12) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi / 2) + (2 * cos(-pi / 12) ** 2 - 1) = -1 + cos(-pi/2) + 2*cos(-pi/12)**2,
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


lemma Trigo_839_test : -(cos(-pi/2)*cos(pi/3) - sin(-pi/2)*sin(pi/3))*sin(611*pi/6)=sin(pi/3) / 2 + sin(0) / 2:=
begin
have : -sin(611 * pi / 6) * (-sin(-pi / 2) * sin(pi / 3) + cos(-pi / 2) * cos(pi / 3)) = -(cos(-pi/2)*cos(pi/3) - sin(-pi/2)*sin(pi/3))*sin(611*pi/6),
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
have : sin(pi/6) = -sin(611*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) * cos(-pi/6) = sin(pi/3) / 2 + sin(0) / 2,
{
rw sin_mul_cos,
have : sin((pi/6) + (-pi/6)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/6) - (-pi/6)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_840_test (h0 : cos(145*pi)≠ 0) (h1 : (2*cos(145*pi))≠ 0) : sin(290*pi)/(2*cos(145*pi))=0:=
begin
have : sin(145*pi) = sin(290*pi) / ( 2 * cos(145*pi) ),
{
have : sin(290*pi) = sin(2*(145*pi)),
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
have : sin(pi) = sin(145*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (72),
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


lemma Trigo_841_test (h0 : cos((-pi)/2)≠ 0) (h1 : sin(-pi)≠ 0) (h2 : (2*sin(-pi/2)*cos(-pi/2))≠ 0) : (1 - cos(-pi))/(2*sin(-pi/2)*cos(-pi/2))=- 1 / tan(32*pi):=
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
have : tan(-pi/2) = - 1 / tan(32*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_842_test (h0 : tan(58*pi)≠ 0) (h1 : (1/tan((-13)*pi/2))≠ 0) (h2 : tan((-13)*pi/2)≠ 0) : tan(-13*pi/2)=- 1 / tan(76*pi):=
begin
have : 1 / (1 / tan((-13) * pi / 2)) = tan(-13*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(58*pi) = 1 / tan(-13*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (58*pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = 1 / tan(58*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/2) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - 1 / tan(76*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_843_test : sin(463*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(701*pi/12) = sin(463*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (701*pi/12) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(701*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (29),
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


lemma Trigo_844_test : -sin(-pi/2)*sin(-pi/6) + (cos(-pi/2)*cos(pi/3) - sin(-pi/2)*sin(pi/3))*cos(-pi/2)=1 - 2 * sin(-pi/3) ** 2:=
begin
have : -sin(-pi / 2) * sin(-pi / 6) + cos(-pi / 2) * (-sin(-pi / 2) * sin(pi / 3) + cos(-pi / 2) * cos(pi / 3)) = -sin(-pi/2)*sin(-pi/6) + (cos(-pi/2)*cos(pi/3) - sin(-pi/2)*sin(pi/3))*cos(-pi/2),
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
have : -sin(-pi / 6) * sin(-pi / 2) + cos(-pi / 6) * cos(-pi / 2) = -sin(-pi/2)*sin(-pi/6) + cos(-pi/2)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = -sin(-pi/6) * sin(-pi/2) + cos(-pi/6) * cos(-pi/2),
{
have : cos(-2*pi/3) = cos((-pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_845_test (h0 : sin(-pi/3)≠ 0) (h1 : (2*sin(-pi/3))≠ 0) : sin(pi/6) ** 2=1 - (sin(-2*pi/3)*cos(pi/2)/(2*sin(-pi/3)) - sin(-pi/3)*sin(pi/2))**2:=
begin
have : 1 - (sin((-2) * pi / 3) / (2 * sin(-pi / 3)) * cos(pi / 2) - sin(-pi / 3) * sin(pi / 2)) ** 2 = 1 - (sin(-2*pi/3)*cos(pi/2)/(2*sin(-pi/3)) - sin(-pi/3)*sin(pi/2))**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : 1 - (-sin(-pi / 3) * sin(pi / 2) + cos(-pi / 3) * cos(pi / 2)) ** 2 = 1 - (cos(-pi/3)*cos(pi/2) - sin(-pi/3)*sin(pi/2))**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/6) = -sin(-pi/3) * sin(pi/2) + cos(-pi/3) * cos(pi/2),
{
have : cos(pi/6) = cos((-pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) ** 2 = 1 - cos(pi/6) ** 2,
{
rw sin_sq,
},
rw this,
end


lemma Trigo_846_test : cos(137*pi)**2=1 / 2 - cos(pi) / 2:=
begin
have : (-cos(137 * pi)) ** 2 = cos(137*pi)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(28*pi) = -cos(137*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (28*pi) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(28*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (14),
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


lemma Trigo_847_test : cos(0)=-sin(-2*pi)*sin(2*pi) + (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*cos(26*pi):=
begin
have : -sin((-2) * pi) * sin(2 * pi) + (4 * cos((-2) * pi / 3) ** 3 - 3 * cos((-2) * pi / 3)) * cos(26 * pi) = -sin(-2*pi)*sin(2*pi) + (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*cos(26*pi),
{
field_simp at *,
},
have : cos(2*pi) = cos(26*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -sin(2 * pi) * sin((-2) * pi) + cos(2 * pi) * (4 * cos((-2) * pi / 3) ** 3 - 3 * cos((-2) * pi / 3)) = -sin(-2*pi)*sin(2*pi) + (4*cos(-2*pi/3)**3 - 3*cos(-2*pi/3))*cos(2*pi),
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
have : cos(0) = - sin(2*pi) * sin(-2*pi) + cos(2*pi) * cos(-2*pi),
{
have : cos(0) = cos((2*pi) + (-2*pi)),
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


lemma Trigo_848_test : -3*cos(19*pi/3) + 4*cos(19*pi/3)**3=- 1:=
begin
have : (-3) * cos(19 * pi / 3) + 4 * cos(19 * pi / 3) ** 3 = -3*cos(19*pi/3) + 4*cos(19*pi/3)**3,
{
field_simp at *,
},
have : cos(pi/3) = cos(19*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (3),
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
have : cos(pi) = - 1,
{
rw cos_pi,
},
rw this,
end


lemma Trigo_849_test : -3*cos(pi/3)**2 + 4*(-sin(pi/3)**2 + cos(pi/3)**2)**3 + 3*sin(pi/3)**2=- cos(161*pi):=
begin
have : 4 * (-sin(pi / 3) ** 2 + cos(pi / 3) ** 2) ** 3 - 3 * (-sin(pi / 3) ** 2 + cos(pi / 3) ** 2) = -3*cos(pi/3)**2 + 4*(-sin(pi/3)**2 + cos(pi/3)**2)**3 + 3*sin(pi/3)**2,
{
field_simp at *,
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
have : cos(2*pi) = - cos(161*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_850_test : cos(-5*pi/2)*cos(-2*pi) + sin(-5*pi/2)*cos(351*pi/2)=4 * cos(-pi/6) ** 3 - 3 * cos(-pi/6):=
begin
have : sin((-5) * pi / 2) * cos(351 * pi / 2) + cos((-5) * pi / 2) * cos((-2) * pi) = cos(-5*pi/2)*cos(-2*pi) + sin(-5*pi/2)*cos(351*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = cos(351*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-5) * pi / 2) * sin((-2) * pi) + cos((-5) * pi / 2) * cos((-2) * pi) = sin(-5*pi/2)*sin(-2*pi) + cos(-5*pi/2)*cos(-2*pi),
{
field_simp at *,
},
have : cos(-pi/2) = sin(-5*pi/2) * sin(-2*pi) + cos(-5*pi/2) * cos(-2*pi),
{
have : cos(-pi/2) = cos((-5*pi/2) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
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


lemma Trigo_851_test : -3*sin(98*pi/9) + 4*sin(98*pi/9)**3=cos(905*pi/6):=
begin
have : -((-4) * sin(98 * pi / 9) ** 3 + 3 * sin(98 * pi / 9)) = -3*sin(98*pi/9) + 4*sin(98*pi/9)**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(98*pi/3) = -4 * sin(98*pi/9) ** 3 + 3 * sin(98*pi/9),
{
have : sin(98*pi/3) = sin(3*(98*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(98*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-pi/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = cos(905*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/3) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_852_test : cos(291*pi/2)=-cos(363*pi/2):=
begin
have : sin(3*pi) = cos(363*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (3*pi) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) = cos(291*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(3*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_853_test (h0 : cos(41*pi/2)≠ 0) (h1 : (2*cos(41*pi/2))≠ 0) : sin(41*pi)/(2*cos(41*pi/2))=sin(381*pi/2):=
begin
have : sin(41*pi/2) = sin(41*pi) / ( 2 * cos(41*pi/2) ),
{
have : sin(41*pi) = sin(2*(41*pi/2)),
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
have : cos(-2*pi) = sin(41*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(381*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*pi) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_854_test (h0 : cos(308*pi/3)≠ 0) (h1 : -cos(308*pi/3)≠ 0) (h2 : tan(43*pi/6)≠ 0) : 1/tan(43*pi/6)=-sin(pi/3)/cos(308*pi/3):=
begin
have : tan(pi/3) = 1 / tan(43*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/3) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) / -cos(308 * pi / 3) = -sin(pi/3)/cos(308*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(308*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/3) (51),
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


lemma Trigo_855_test (h0 : cos(0)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(0)*tan(-pi/3))≠ 0) (h3 : (tan(0)*tan(-pi/3)+1)≠ 0) (h4 : cos(-pi/2)≠ 0) (h5 : cos(-pi/6)≠ 0) (h6 : ((tan(-pi/2)-tan(-pi/6))*tan(0)/(1+tan(-pi/2)*tan(-pi/6))+1)≠ 0) (h7 : (1+tan(-pi/2)*tan(-pi/6))≠ 0) (h8 : (tan(0)*((tan(-pi/2)-tan(-pi/6))/(1+tan(-pi/2)*tan(-pi/6)))+1)≠ 0) : (-(tan(-pi/2) - tan(-pi/6))/(1 + tan(-pi/2)*tan(-pi/6)) + tan(0))/((tan(-pi/2) - tan(-pi/6))*tan(0)/(1 + tan(-pi/2)*tan(-pi/6)) + 1)=sqrt( 3 ):=
begin
have : (tan(0) - (tan(-pi / 2) - tan(-pi / 6)) / (1 + tan(-pi / 2) * tan(-pi / 6))) / (tan(0) * ((tan(-pi / 2) - tan(-pi / 6)) / (1 + tan(-pi / 2) * tan(-pi / 6))) + 1) = (-(tan(-pi/2) - tan(-pi/6))/(1 + tan(-pi/2)*tan(-pi/6)) + tan(0))/((tan(-pi/2) - tan(-pi/6))*tan(0)/(1 + tan(-pi/2)*tan(-pi/6)) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
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


lemma Trigo_856_test : (sin(pi/2)*cos(-pi/2) - sin(-pi/2)*cos(pi/2))*sin(2*pi)=cos(pi)/2 + sin(189*pi/2)/2:=
begin
have : sin(2 * pi) * (sin(pi / 2) * cos(-pi / 2) - sin(-pi / 2) * cos(pi / 2)) = (sin(pi/2)*cos(-pi/2) - sin(-pi/2)*cos(pi/2))*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(pi/2) * cos(-pi/2) - sin(-pi/2) * cos(pi/2),
{
have : sin(pi) = sin((pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) / 2 - -sin(189 * pi / 2) / 2 = cos(pi)/2 + sin(189*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi) = -sin(189*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * sin(pi) = cos(pi) / 2 - cos(3*pi) / 2,
{
rw sin_mul_sin,
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
rw this,
end


lemma Trigo_857_test : sin(-349*pi/3)=sin(pi) * cos(-pi/3) - sin(-pi/3) * cos(pi):=
begin
have : - -sin((-349) * pi / 3) = sin(-349*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(487*pi/3) = -sin(-349*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (487*pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/3) = -sin(487*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_858_test : -sin(-pi/6)**2 + cos(-pi/6)**2=-2*sin(635*pi/12)*cos(635*pi/12):=
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
have : -(2 * sin(635 * pi / 12) * cos(635 * pi / 12)) = -2*sin(635*pi/12)*cos(635*pi/12),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(635*pi/6) = 2 * sin(635*pi/12) * cos(635*pi/12),
{
have : sin(635*pi/6) = sin(2*(635*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = - sin(635*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_859_test : cos(373*pi/6)=sqrt( 3 ) / 2:=
begin
have : - -cos(373 * pi / 6) = cos(373*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(280*pi/3) = -cos(373*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (280*pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(280*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/3) (47),
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


lemma Trigo_860_test : cos(pi) + sin(pi/6)=-2*sin(-pi/6)*cos(400*pi/3):=
begin
have : sin(pi / 6) + cos(pi) = cos(pi) + sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(-pi / 6) * -cos(400 * pi / 3) = -2*sin(-pi/6)*cos(400*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = -cos(400*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) + sin(-pi/2) = 2 * sin(-pi/6) * cos(pi/3),
{
rw sin_add_sin,
have : sin(((pi/6) + (-pi/2))/2) = sin(-pi/6),
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
},
rw this,
end


lemma Trigo_861_test : sin(-439*pi/6)=- sin(743*pi/6):=
begin
have : sin((-439) * pi / 6) = sin(-439*pi/6),
{
field_simp at *,
},
have : sin(1033*pi/6) = sin(-439*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (1033*pi/6) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = sin(1033*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - sin(743*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_862_test (h0 : cos(-pi/6)≠ 0) (h1 : (1-2*sin(-pi/12)**2)≠ 0) : sin(-pi/6)/(1 - 2*sin(-pi/12)**2)=1 / tan(185*pi/3):=
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
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/6) = 1 / tan(185*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_863_test : cos(-469*pi/6)=- sin(pi/3) * sin(-pi/6) + cos(pi/3) * cos(-pi/6):=
begin
have : cos((-469) * pi / 6) = cos(-469*pi/6),
{
field_simp at *,
},
have : cos(889*pi/6) = cos(-469*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (889*pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(889*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/6) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = - sin(pi/3) * sin(-pi/6) + cos(pi/3) * cos(-pi/6),
{
have : cos(pi/6) = cos((pi/3) + (-pi/6)),
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


lemma Trigo_864_test : sin(-pi) ** 2=1 - cos(193*pi)**2:=
begin
have : cos(143*pi) = cos(193*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (143*pi) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi) = cos(143*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (72),
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


lemma Trigo_865_test (h0 : cos(81*pi)≠ 0) : -sin(81*pi)/cos(81*pi)=tan(62*pi):=
begin
have : -(sin(81 * pi) / cos(81 * pi)) = -sin(81*pi)/cos(81*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(81*pi) = sin(81*pi) / cos(81*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = -tan(81*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi) = tan(62*pi),
{
rw tan_eq_tan_add_int_mul_pi (-pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_866_test : -2*sin(773*pi/6)**2 + 1 - cos(-pi)=- 2 * sin(2*pi/3) * sin(-pi/3):=
begin
have : (-2) * sin(773 * pi / 6) ** 2 + 1 - cos(-pi) = -2*sin(773*pi/6)**2 + 1 - cos(-pi),
{
field_simp at *,
},
have : sin(pi/6) = sin(773*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * sin(pi / 6) ** 2 - cos(-pi) = -2*sin(pi/6)**2 + 1 - cos(-pi),
{
field_simp at *,
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


lemma Trigo_867_test : -sin(pi/6)*cos(2*pi/3) - sin(413*pi/3)*cos(pi/6)=1:=
begin
have : -sin(pi / 6) * cos(2 * pi / 3) + -sin(413 * pi / 3) * cos(pi / 6) = -sin(pi/6)*cos(2*pi/3) - sin(413*pi/3)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(413*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_868_test : -(sin(11*pi/6)*cos(-2*pi) + sin(-2*pi)*cos(11*pi/6))**2 + cos(-pi/6)**2=cos(353*pi/3):=
begin
have : -(sin(11 * pi / 6) * cos((-2) * pi) + sin((-2) * pi) * cos(11 * pi / 6)) ** 2 + cos(-pi / 6) ** 2 = -(sin(11*pi/6)*cos(-2*pi) + sin(-2*pi)*cos(11*pi/6))**2 + cos(-pi/6)**2,
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
have : cos(-pi/3) = cos(353*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_869_test : cos(2*pi)=cos(-102*pi):=
begin
have : cos((-102) * pi) = cos(-102*pi),
{
field_simp at *,
},
have : sin(-211*pi/2) = cos(-102*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-211*pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : - -sin((-211) * pi / 2) = sin(-211*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(331*pi/2) = -sin(-211*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (331*pi/2) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(331*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_870_test : sin(-735*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -sin((-735) * pi / 4) = sin(-735*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(759*pi/4) = -sin(-735*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (759*pi/4) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(759*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (94),
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


lemma Trigo_871_test : sin(155*pi/2)/2 + sin(5*pi/2)/2=sin(3*pi/2) / 2 + sin(5*pi/2) / 2:=
begin
have : - -sin(155 * pi / 2) / 2 + sin(5 * pi / 2) / 2 = sin(155*pi/2)/2 + sin(5*pi/2)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-3*pi/2) = -sin(155*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-3*pi/2) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-3) * pi / 2) / 2 + sin(5 * pi / 2) / 2 = -sin(-3*pi/2)/2 + sin(5*pi/2)/2,
{
field_simp at *,
},
have : sin(2*pi) * cos(pi/2) = -sin(-3*pi/2) / 2 + sin(5*pi/2) / 2,
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
conv {to_lhs, rw ← this,},
have : (sin(2*pi) * cos(pi/2)) = sin(2*pi)*cos(pi/2),
{
ring,
},
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
rw this,
end


lemma Trigo_872_test : -cos(132*pi)=- cos(100*pi):=
begin
have : cos(63*pi) = -cos(132*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (63*pi) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = cos(63*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (pi) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = - cos(100*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_873_test : -sin(11*pi/12)**2 + cos(11*pi/12)**2=-cos(13*pi/6)/2 + cos(11*pi/6)/2 + cos(-pi/6)*cos(2*pi):=
begin
have : -(cos(13 * pi / 6) / 2 - cos(11 * pi / 6) / 2) + cos(2 * pi) * cos(-pi / 6) = -cos(13*pi/6)/2 + cos(11*pi/6)/2 + cos(-pi/6)*cos(2*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) * sin(-pi/6) = cos(13*pi/6) / 2 - cos(11*pi/6) / 2,
{
rw sin_mul_sin,
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
conv {to_rhs, rw ← this,},
have : -(sin(2*pi) * sin(-pi/6)) = -sin(2*pi)*sin(-pi/6),
{
ring,
},
conv {to_rhs, rw this,},
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


lemma Trigo_874_test : -sin(1111*pi/6)*cos(pi/2) - sin(pi/2)*cos(1111*pi/6)=sqrt( 3 ) / 2:=
begin
have : -(sin(1111 * pi / 6) * cos(pi / 2) + sin(pi / 2) * cos(1111 * pi / 6)) = -sin(1111*pi/6)*cos(pi/2) - sin(pi/2)*cos(1111*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(557*pi/3) = sin(1111*pi/6) * cos(pi/2) + sin(pi/2) * cos(1111*pi/6),
{
have : sin(557*pi/3) = sin((1111*pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(557*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (92),
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


lemma Trigo_875_test : -sin(673*pi/12)**2 + cos(pi/12)**2=sqrt( 3 ) / 2:=
begin
have : sin(pi/12) = sin(673*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (28),
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_876_test : sin(565*pi/6)*cos(-pi/3) - sin(-pi/3)*cos(565*pi/6)=4 * cos(2*pi) ** 3 - 3 * cos(2*pi):=
begin
have : sin(189*pi/2) = sin(565*pi/6) * cos(-pi/3) - sin(-pi/3) * cos(565*pi/6),
{
have : sin(189*pi/2) = sin((565*pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(6*pi) = sin(189*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (6*pi) (50),
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


lemma Trigo_877_test : 1 - 2*sin(115*pi/2)**2=4 * cos(pi) ** 3 - 3 * cos(pi):=
begin
have : sin(3*pi/2) = sin(115*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (3*pi/2) (28),
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


lemma Trigo_878_test : 1 - 2*(-sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi))**2=- sin(359*pi/2):=
begin
have : 1 - 2 * (sin(3 * pi) * cos(2 * pi) - sin(2 * pi) * cos(3 * pi)) ** 2 = 1 - 2*(-sin(2*pi)*cos(3*pi) + sin(3*pi)*cos(2*pi))**2,
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
have : cos(2*pi) = - sin(359*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_879_test (h0 : cos((pi/2)/2)≠ 0) (h1 : sin(pi/2)≠ 0) : (1 - cos(73*pi/2))/sin(pi/2)=1:=
begin
have : cos(pi/2) = cos(73*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/2) (18),
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


lemma Trigo_880_test : -sin(-pi/3)*cos(823*pi/6) + sin(823*pi/6)*cos(-pi/3)=cos(45*pi):=
begin
have : sin(823 * pi / 6) * cos(-pi / 3) - sin(-pi / 3) * cos(823 * pi / 6) = -sin(-pi/3)*cos(823*pi/6) + sin(823*pi/6)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(275*pi/2) = sin(823*pi/6) * cos(-pi/3) - sin(-pi/3) * cos(823*pi/6),
{
have : sin(275*pi/2) = sin((823*pi/6) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(275*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(45*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_881_test : 4*cos(1177*pi/9)**3 - 3*cos(1177*pi/9)=1 / 2:=
begin
have : (-4) * (-cos(1177 * pi / 9)) ** 3 + 3 * -cos(1177 * pi / 9) = 4*cos(1177*pi/9)**3 - 3*cos(1177*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = -cos(1177*pi/9),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (65),
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


lemma Trigo_882_test : -cos(145*pi/2)*cos(120*pi)=cos(5*pi/2) / 2 - cos(-3*pi/2) / 2:=
begin
have : sin(-2*pi) = -cos(145*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(120 * pi) * sin((-2) * pi) = sin(-2*pi)*cos(120*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(120*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_883_test : (sin(pi/2)*cos(-3*pi/2) + sin(-3*pi/2)*cos(pi/2))*sin(pi)=-cos(0)/2 - cos(119*pi)/2:=
begin
have : sin(pi) * (sin((-3) * pi / 2) * cos(pi / 2) + sin(pi / 2) * cos((-3) * pi / 2)) = (sin(pi/2)*cos(-3*pi/2) + sin(-3*pi/2)*cos(pi/2))*sin(pi),
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
have : -cos(119 * pi) / 2 - cos(0) / 2 = -cos(0)/2 - cos(119*pi)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = -cos(119*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi) * sin(-pi) = cos(2*pi) / 2 - cos(0) / 2,
{
rw sin_mul_sin,
have : cos((pi) + (-pi)) = cos(0),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi) - (-pi)) = cos(2*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_884_test : -sin(pi/2)**2 + cos(pi/2)**2 + cos(-pi/6)=cos(pi) + cos(-pi/6):=
begin
have : 2 * (cos(-pi / 6) / 2 + cos(pi) / 2) = cos(pi) + cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(5*pi/12) * cos(7*pi/12) = cos(-pi/6) / 2 + cos(pi) / 2,
{
rw cos_mul_cos,
have : cos((5*pi/12) + (7*pi/12)) = cos(pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/12) - (7*pi/12)) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(cos(5*pi/12) * cos(7*pi/12)) = 2*cos(7*pi/12)*cos(5*pi/12),
{
ring,
},
conv {to_rhs, rw this,},
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
have : cos(pi) + cos(-pi/6) = 2 * cos(7*pi/12) * cos(5*pi/12),
{
rw cos_add_cos,
have : cos(((pi) + (-pi/6))/2) = cos(5*pi/12),
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
ring,
},
rw this,
end


lemma Trigo_885_test : -cos(-177*pi/2)=0:=
begin
have : -cos((-177) * pi / 2) = -cos(-177*pi/2),
{
field_simp at *,
},
have : cos(247*pi/2) = -cos(-177*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (247*pi/2) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(247*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi) (62),
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


lemma Trigo_886_test : sin(pi/2)=(1 - 2*sin(-pi/4)**2)*cos(349*pi/2) - sin(-pi/2)*sin(349*pi/2):=
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
conv {to_rhs, rw ← this,},
have : -sin(349 * pi / 2) * sin(-pi / 2) + cos(349 * pi / 2) * cos(-pi / 2) = cos(-pi/2)*cos(349*pi/2) - sin(-pi/2)*sin(349*pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(174*pi) = -sin(349*pi/2) * sin(-pi/2) + cos(349*pi/2) * cos(-pi/2),
{
have : cos(174*pi) = cos((349*pi/2) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = cos(174*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_887_test (h0 : cos(261*pi/2)≠ 0) (h1 : (2*cos(261*pi/2))≠ 0) : -sin(261*pi)/(2*cos(261*pi/2))=- 1:=
begin
have : -(sin(261 * pi) / (2 * cos(261 * pi / 2))) = -sin(261*pi)/(2*cos(261*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(261*pi/2) = sin(261*pi) / ( 2 * cos(261*pi/2) ),
{
have : sin(261*pi) = sin(2*(261*pi/2)),
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
have : cos(pi) = -sin(261*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (65),
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


lemma Trigo_888_test : -cos(4285*pi/24)**2 + cos(pi/24)**2=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : -(-cos(4285 * pi / 24)) ** 2 + cos(pi / 24) ** 2 = -cos(4285*pi/24)**2 + cos(pi/24)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/24) = -cos(4285*pi/24),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/24) (89),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_889_test : -sin(-2*pi)*sin(5*pi/3) - sin(547*pi/6)*cos(-2*pi)=2 * cos(-pi/6) ** 2 - 1:=
begin
have : -sin((-2) * pi) * sin(5 * pi / 3) + cos((-2) * pi) * -sin(547 * pi / 6) = -sin(-2*pi)*sin(5*pi/3) - sin(547*pi/6)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/3) = -sin(547*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/3) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 3) * sin((-2) * pi) + cos(5 * pi / 3) * cos((-2) * pi) = -sin(-2*pi)*sin(5*pi/3) + cos(-2*pi)*cos(5*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(5*pi/3) * sin(-2*pi) + cos(5*pi/3) * cos(-2*pi),
{
have : cos(-pi/3) = cos((5*pi/3) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_890_test : -8*sin(pi/48)**2*cos(pi/48)**2 + 1=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : 1 - 2 * (2 * sin(pi / 48) * cos(pi / 48)) ** 2 = -8*sin(pi/48)**2*cos(pi/48)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/24) = 2 * sin(pi/48) * cos(pi/48),
{
have : sin(pi/24) = sin(2*(pi/48)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
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


lemma Trigo_891_test : 2*(sin(-pi/6)*cos(pi/3) + sin(pi/3)*cos(-pi/6))*cos(pi/6)=- sin(599*pi/3):=
begin
have : sin(pi/6) = sin(-pi/6) * cos(pi/3) + sin(pi/3) * cos(-pi/6),
{
have : sin(pi/6) = sin((-pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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
have : sin(pi/3) = - sin(599*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (100),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_892_test : sin(3*pi/2)*cos(2*pi) + sin(73*pi)*cos(3*pi/2)=sin(203*pi/2):=
begin
have : sin(3 * pi / 2) * cos(2 * pi) - -sin(73 * pi) * cos(3 * pi / 2) = sin(3*pi/2)*cos(2*pi) + sin(73*pi)*cos(3*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(73*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(3*pi/2) * cos(2*pi) - sin(2*pi) * cos(3*pi/2),
{
have : sin(-pi/2) = sin((3*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = sin(203*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_893_test (h0 : cos(595*pi/3)≠ 0) (h1 : cos(pi/3)≠ 0) : sin(pi/3)/cos(595*pi/3)=sin(pi/3)/cos(pi/3):=
begin
have : tan(pi/3) = sin(pi/3) / cos(pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_rhs, rw ← this,},
have : cos(pi/3) = cos(595*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/3) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_894_test : -cos(317*pi/3)=cos(568*pi/3):=
begin
have : cos(314*pi/3) = -cos(317*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (314*pi/3) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(314*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(568*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_895_test (h0 : cos(-pi/2)≠ 0) (h1 : (2*cos(-pi/2))≠ 0) : (sin(pi/3)*cos(-4*pi/3) + sin(-4*pi/3)*cos(pi/3))/(2*cos(-pi/2))=- sin(45*pi/2):=
begin
have : (sin((-4) * pi / 3) * cos(pi / 3) + sin(pi / 3) * cos((-4) * pi / 3)) / (2 * cos(-pi / 2)) = (sin(pi/3)*cos(-4*pi/3) + sin(-4*pi/3)*cos(pi/3))/(2*cos(-pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(-4*pi/3) * cos(pi/3) + sin(pi/3) * cos(-4*pi/3),
{
have : sin(-pi) = sin((-4*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
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
have : sin(-pi/2) = - sin(45*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_896_test : -3 + 6*sin(pi/12)**2 + 4*(1 - 2*sin(pi/12)**2)**3=0:=
begin
have : (-3) * (1 - 2 * sin(pi / 12) ** 2) + 4 * (1 - 2 * sin(pi / 12) ** 2) ** 3 = -3 + 6*sin(pi/12)**2 + 4*(1 - 2*sin(pi/12)**2)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_897_test (h0 : cos(-pi/4)≠ 0) (h1 : (1-tan(-pi/4)**2)≠ 0) (h2 : cos(-pi/12)≠ 0) (h3 : cos(pi/6)≠ 0) (h4 : (tan(-pi/12)*tan(pi/6)+1)≠ 0) (h5 : (1+tan(-pi/12)*tan(pi/6))≠ 0) (h6 : ((-(-tan(pi/6)+tan(-pi/12))**2/(tan(-pi/12)*tan(pi/6)+1)**2+1)*(tan(-pi/12)*tan(pi/6)+1))≠ 0) (h7 : (1-((tan(-pi/12)-tan(pi/6))/(1+tan(-pi/12)*tan(pi/6)))**2)≠ 0) : 2*(-tan(pi/6) + tan(-pi/12))/((-(-tan(pi/6) + tan(-pi/12))**2/(tan(-pi/12)*tan(pi/6) + 1)**2 + 1)*(tan(-pi/12)*tan(pi/6) + 1))=- 1 / tan(35*pi):=
begin
have : 2 * ((tan(-pi / 12) - tan(pi / 6)) / (1 + tan(-pi / 12) * tan(pi / 6))) / (1 - ((tan(-pi / 12) - tan(pi / 6)) / (1 + tan(-pi / 12) * tan(pi / 6))) ** 2) = 2*(-tan(pi/6) + tan(-pi/12))/((-(-tan(pi/6) + tan(-pi/12))**2/(tan(-pi/12)*tan(pi/6) + 1)**2 + 1)*(tan(-pi/12)*tan(pi/6) + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/4) = ( tan(-pi/12) - tan(pi/6) ) / ( 1 + tan(-pi/12) * tan(pi/6) ),
{
have : tan(-pi/4) = tan((-pi/12) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = 2 * tan(-pi/4) / ( 1 - tan(-pi/4) ** 2 ),
{
have : tan(-pi/2) = tan(2*(-pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/2) = - 1 / tan(35*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/2) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_898_test : 1 - sin(-2*pi)**2=1 - (-sin(pi/3)*cos(-5*pi/3) + sin(-5*pi/3)*cos(pi/3))**2:=
begin
have : 1 - sin((-2) * pi) ** 2 = 1 - sin(-2*pi)**2,
{
field_simp at *,
},
have : cos(-2*pi) ** 2 = 1 - sin(-2*pi) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : 1 - (sin((-5) * pi / 3) * cos(pi / 3) - sin(pi / 3) * cos((-5) * pi / 3)) ** 2 = 1 - (-sin(pi/3)*cos(-5*pi/3) + sin(-5*pi/3)*cos(pi/3))**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) = sin(-5*pi/3) * cos(pi/3) - sin(pi/3) * cos(-5*pi/3),
{
have : sin(-2*pi) = sin((-5*pi/3) - (pi/3)),
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


lemma Trigo_899_test : -3*cos(42*pi) + 4*cos(42*pi)**3=1:=
begin
have : 4 * cos(42 * pi) ** 3 - 3 * cos(42 * pi) = -3*cos(42*pi) + 4*cos(42*pi)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(126*pi) = 4 * cos(42*pi) ** 3 - 3 * cos(42*pi),
{
have : cos(126*pi) = cos(3*(42*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(126*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (62),
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


lemma Trigo_900_test : 2*sin(95*pi/6)*cos(95*pi/6)=- sqrt( 3 ) / 2:=
begin
have : sin(95*pi/3) = 2 * sin(95*pi/6) * cos(95*pi/6),
{
have : sin(95*pi/3) = sin(2*(95*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = sin(95*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/6) (16),
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


lemma Trigo_901_test (h0 : cos(-2*pi/3)≠ 0) (h1 : (2*cos((-2)*pi/3))≠ 0) (h2 : (2*cos(-2*pi/3))≠ 0) : sin(-4*pi/3)*cos(pi/3)/(2*cos(-2*pi/3)) - sin(pi/3)*cos(-2*pi/3)=- sin(147*pi):=
begin
have : sin((-4) * pi / 3) / (2 * cos((-2) * pi / 3)) * cos(pi / 3) - sin(pi / 3) * cos((-2) * pi / 3) = sin(-4*pi/3)*cos(pi/3)/(2*cos(-2*pi/3)) - sin(pi/3)*cos(-2*pi/3),
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
have : sin((-2) * pi / 3) * cos(pi / 3) - sin(pi / 3) * cos((-2) * pi / 3) = sin(-2*pi/3)*cos(pi/3) - sin(pi/3)*cos(-2*pi/3),
{
field_simp at *,
},
have : sin(-pi) = sin(-2*pi/3) * cos(pi/3) - sin(pi/3) * cos(-2*pi/3),
{
have : sin(-pi) = sin((-2*pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - sin(147*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_902_test : cos(2*pi)=-4*sin(641*pi/6)**3 + 3*sin(641*pi/6):=
begin
have : (-4) * sin(641 * pi / 6) ** 3 + 3 * sin(641 * pi / 6) = -4*sin(641*pi/6)**3 + 3*sin(641*pi/6),
{
field_simp at *,
},
have : sin(641*pi/2) = -4 * sin(641*pi/6) ** 3 + 3 * sin(641*pi/6),
{
have : sin(641*pi/2) = sin(3*(641*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : - -sin(641 * pi / 2) = sin(641*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(391*pi/2) = -sin(641*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (391*pi/2) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(391*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_903_test : (-4*cos(61*pi/6)**3 + 3*cos(61*pi/6))*cos(-pi/2)=- sin(-5*pi/2) / 2 + sin(3*pi/2) / 2:=
begin
have : ((-4) * cos(61 * pi / 6) ** 3 + 3 * cos(61 * pi / 6)) * cos(-pi / 2) = (-4*cos(61*pi/6)**3 + 3*cos(61*pi/6))*cos(-pi/2),
{
field_simp at *,
},
have : sin(2*pi/3) = cos(61*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(2 * pi / 3) ** 3 + 3 * sin(2 * pi / 3)) * cos(-pi / 2) = (-4*sin(2*pi/3)**3 + 3*sin(2*pi/3))*cos(-pi/2),
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
have : sin(2*pi) * cos(-pi/2) = - sin(-5*pi/2) / 2 + sin(3*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-pi/2) + (2*pi)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/2) - (2*pi)) = sin(-5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_904_test : sin(-5*pi/2)=sin(-pi/2)*sin(289*pi/2) - sin(-2*pi)*sin(141*pi):=
begin
have : sin(-pi / 2) * sin(289 * pi / 2) - sin((-2) * pi) * sin(141 * pi) = sin(-pi/2)*sin(289*pi/2) - sin(-2*pi)*sin(141*pi),
{
field_simp at *,
},
have : cos(-2*pi) = sin(289*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin((-2) * pi) * -sin(141 * pi) + sin(-pi / 2) * cos((-2) * pi) = sin(-pi/2)*cos(-2*pi) - sin(-2*pi)*sin(141*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -sin(141*pi),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-5*pi/2) = sin(-2*pi) * cos(-pi/2) + sin(-pi/2) * cos(-2*pi),
{
have : sin(-5*pi/2) = sin((-2*pi) + (-pi/2)),
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


lemma Trigo_905_test : -1 + sin(97*pi/6) + 2*cos(-pi/12)**2=2 * cos(-pi/12) * cos(-pi/4):=
begin
have : sin(97 * pi / 6) + (2 * cos(-pi / 12) ** 2 - 1) = -1 + sin(97*pi/6) + 2*cos(-pi/12)**2,
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
have : cos(-pi/3) = sin(97*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/3) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) + cos(-pi/6) = 2 * cos(-pi/12) * cos(-pi/4),
{
rw cos_add_cos,
have : cos(((-pi/3) + (-pi/6))/2) = cos(-pi/4),
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
ring,
},
rw this,
end


lemma Trigo_906_test : 1 - 2*(sin(-2*pi)*cos(pi) + sin(pi)*cos(-2*pi))**2=- cos(61*pi):=
begin
have : 1 - 2 * (sin(pi) * cos((-2) * pi) + sin((-2) * pi) * cos(pi)) ** 2 = 1 - 2*(sin(-2*pi)*cos(pi) + sin(pi)*cos(-2*pi))**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(pi) * cos(-2*pi) + sin(-2*pi) * cos(pi),
{
have : sin(-pi) = sin((pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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
have : cos(-2*pi) = - cos(61*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-2*pi) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_907_test : cos(655*pi/4)=sqrt( 2 ) / 2:=
begin
have : sin(521*pi/4) = cos(655*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (521*pi/4) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(521*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (65),
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


lemma Trigo_908_test : -sin(-223*pi/2)=- 1:=
begin
have : -sin((-223) * pi / 2) = -sin(-223*pi/2),
{
field_simp at *,
},
have : sin(239*pi/2) = -sin(-223*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (239*pi/2) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(239*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi) (60),
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


lemma Trigo_909_test (h0 : sin(587*pi/6)≠ 0) (h1 : (2*sin(587*pi/6))≠ 0) : -sin(587*pi/3)/(2*sin(587*pi/6))=- sqrt( 3 ) / 2:=
begin
have : -(sin(587 * pi / 3) / (2 * sin(587 * pi / 6))) = -sin(587*pi/3)/(2*sin(587*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(587*pi/6) = sin(587*pi/3) / ( 2 * sin(587*pi/6) ),
{
have : sin(587*pi/3) = sin(2*(587*pi/6)),
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
have : cos(5*pi/6) = -cos(587*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/6) (48),
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


lemma Trigo_910_test : sin(980*pi/3)=sqrt( 3 ) / 2:=
begin
have : - -sin(980 * pi / 3) = sin(980*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(847*pi/6) = -sin(980*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (847*pi/6) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(847*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (70),
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


lemma Trigo_911_test : -sin(-pi/6) - cos(119*pi)=2*sin(pi/3)*sin(55*pi/3):=
begin
have : -cos(119 * pi) - sin(-pi / 6) = -sin(-pi/6) - cos(119*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(119*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(55*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) - sin(-pi/6) = 2 * sin(pi/3) * cos(pi/6),
{
rw sin_sub_sin,
have : cos(((pi/2) + (-pi/6))/2) = cos(pi/6),
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
},
rw this,
end


lemma Trigo_912_test : 3*sin(-pi/3) - 4*sin(-pi/3)**3=-1 + 2*sin(243*pi/4)**2:=
begin
have : -(1 - 2 * sin(243 * pi / 4) ** 2) = -1 + 2*sin(243*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(243*pi/2) = 1 - 2 * sin(243*pi/4) ** 2,
{
have : cos(243*pi/2) = cos(2*(243*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
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
have : sin(-pi) = - cos(243*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_913_test : tan(176*pi)=- 1 / tan(93*pi/2):=
begin
have : tan(78*pi) = tan(176*pi),
{
rw tan_eq_tan_add_int_mul_pi (78*pi) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = tan(78*pi),
{
rw tan_eq_tan_add_int_mul_pi (-2*pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-2*pi) = - 1 / tan(93*pi/2),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-2*pi) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_914_test : -cos(2435*pi/12)=sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : sin(2333*pi/12) = -cos(2435*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2333*pi/12) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_915_test : -sin(pi)*sin(695*pi/6)=-cos(1067*pi/6)/2 - cos(7*pi/6)/2:=
begin
have : -sin(695 * pi / 6) * sin(pi) = -sin(pi)*sin(695*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(695*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/6) = -cos(1067*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-5*pi/6) (88),
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


lemma Trigo_916_test : -cos(430*pi/3)=- sin(863*pi/6):=
begin
have : sin(491*pi/6) = cos(430*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (491*pi/6) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(491*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - sin(863*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_917_test : sin(-pi/6)*cos(139*pi/6) - sin(139*pi/6)*cos(-pi/6)=sin(128*pi/3):=
begin
have : -(sin(139 * pi / 6) * cos(-pi / 6) - sin(-pi / 6) * cos(139 * pi / 6)) = sin(-pi/6)*cos(139*pi/6) - sin(139*pi/6)*cos(-pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(70*pi/3) = sin(139*pi/6) * cos(-pi/6) - sin(-pi/6) * cos(139*pi/6),
{
have : sin(70*pi/3) = sin((139*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = -sin(70*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = sin(128*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_918_test (h0 : tan(441*pi/4)≠ 0) : 1/tan(441*pi/4)=1:=
begin
have : -((-1) / tan(441 * pi / 4)) = 1/tan(441*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(143*pi/4) = -1 / tan(441*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (143*pi/4) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = -tan(143*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/4) (36),
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


lemma Trigo_919_test (h0 : cos(-pi/6)≠ 0) (h1 : cos(-pi/3)≠ 0) (h2 : (1+tan(-pi/6)*tan(-pi/3))≠ 0) (h3 : (tan(-pi/3)*tan(-pi/6)+1)≠ 0) (h4 : cos(-7*pi/3)≠ 0) (h5 : cos(-2*pi)≠ 0) (h6 : (1+tan((-7)*pi/3)*tan((-2)*pi))≠ 0) (h7 : ((tan((-7)*pi/3)-tan((-2)*pi))/(1+tan((-7)*pi/3)*tan((-2)*pi))*tan(-pi/6)+1)≠ 0) (h8 : (tan(-7*pi/3)*tan(-2*pi)+1)≠ 0) (h9 : ((tan(-7*pi/3)-tan(-2*pi))*tan(-pi/6)/(tan(-7*pi/3)*tan(-2*pi)+1)+1)≠ 0) : (tan(-pi/6) - (tan(-7*pi/3) - tan(-2*pi))/(tan(-7*pi/3)*tan(-2*pi) + 1))/((tan(-7*pi/3) - tan(-2*pi))*tan(-pi/6)/(tan(-7*pi/3)*tan(-2*pi) + 1) + 1)=sqrt( 3 ) / 3:=
begin
have : (tan(-pi / 6) - (tan((-7) * pi / 3) - tan((-2) * pi)) / (1 + tan((-7) * pi / 3) * tan((-2) * pi))) / ((tan((-7) * pi / 3) - tan((-2) * pi)) / (1 + tan((-7) * pi / 3) * tan((-2) * pi)) * tan(-pi / 6) + 1) = (tan(-pi/6) - (tan(-7*pi/3) - tan(-2*pi))/(tan(-7*pi/3)*tan(-2*pi) + 1))/((tan(-7*pi/3) - tan(-2*pi))*tan(-pi/6)/(tan(-7*pi/3)*tan(-2*pi) + 1) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = ( tan(-7*pi/3) - tan(-2*pi) ) / ( 1 + tan(-7*pi/3) * tan(-2*pi) ),
{
have : tan(-pi/3) = tan((-7*pi/3) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-pi / 6) - tan(-pi / 3)) / (1 + tan(-pi / 6) * tan(-pi / 3)) = (tan(-pi/6) - tan(-pi/3))/(tan(-pi/3)*tan(-pi/6) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(-pi/6) - tan(-pi/3) ) / ( 1 + tan(-pi/6) * tan(-pi/3) ),
{
have : tan(pi/6) = tan((-pi/6) - (-pi/3)),
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


lemma Trigo_920_test : (sin(-pi)*sin(-2*pi/3) + cos(-pi)*cos(-2*pi/3))*cos(-2*pi/3) - sin(-2*pi/3)*sin(pi/3)=2 * cos(-pi/6) ** 2 - 1:=
begin
have : cos((-2) * pi / 3) * (sin((-2) * pi / 3) * sin(-pi) + cos((-2) * pi / 3) * cos(-pi)) - sin((-2) * pi / 3) * sin(pi / 3) = (sin(-pi)*sin(-2*pi/3) + cos(-pi)*cos(-2*pi/3))*cos(-2*pi/3) - sin(-2*pi/3)*sin(pi/3),
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
have : -sin((-2) * pi / 3) * sin(pi / 3) + cos((-2) * pi / 3) * cos(pi / 3) = cos(-2*pi/3)*cos(pi/3) - sin(-2*pi/3)*sin(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(-2*pi/3) * sin(pi/3) + cos(-2*pi/3) * cos(pi/3),
{
have : cos(-pi/3) = cos((-2*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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


lemma Trigo_921_test (h0 : cos(295*pi/2)≠ 0) (h1 : (2*cos(295*pi/2))≠ 0) : -sin(295*pi)/(2*cos(295*pi/2))=2 * cos(pi) ** 2 - 1:=
begin
have : -(sin(295 * pi) / (2 * cos(295 * pi / 2))) = -sin(295*pi)/(2*cos(295*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(295*pi/2) = sin(295*pi) / ( 2 * cos(295*pi/2) ),
{
have : sin(295*pi) = sin(2*(295*pi/2)),
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
have : cos(2*pi) = -sin(295*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (74),
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


lemma Trigo_922_test : cos(1693*pi/6)=- cos(571*pi/6):=
begin
have : cos(781*pi/6) = cos(1693*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (781*pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(781*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = - cos(571*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_923_test : sin(-7*pi/3)=(-sin(pi)**2 + cos(pi)**2)*sin(-pi/3) + sin(2*pi)*sin(175*pi/6):=
begin
have : sin(-pi / 3) * (-sin(pi) ** 2 + cos(pi) ** 2) + sin(2 * pi) * sin(175 * pi / 6) = (-sin(pi)**2 + cos(pi)**2)*sin(-pi/3) + sin(2*pi)*sin(175*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-pi / 3) * cos(2 * pi) - sin(2 * pi) * -sin(175 * pi / 6) = sin(-pi/3)*cos(2*pi) + sin(2*pi)*sin(175*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/3) = -sin(175*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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


lemma Trigo_924_test (h0 : cos(329*pi/6)≠ 0) (h1 : cos(pi)≠ 0) (h2 : (1+tan(329*pi/6)*tan(pi))≠ 0) (h3 : (tan(pi)*tan(329*pi/6)+1)≠ 0) : -(tan(329*pi/6) - tan(pi))/(tan(pi)*tan(329*pi/6) + 1)=1 / tan(217*pi/3):=
begin
have : -((tan(329 * pi / 6) - tan(pi)) / (1 + tan(329 * pi / 6) * tan(pi))) = -(tan(329*pi/6) - tan(pi))/(tan(pi)*tan(329*pi/6) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(323*pi/6) = ( tan(329*pi/6) - tan(pi) ) / ( 1 + tan(329*pi/6) * tan(pi) ),
{
have : tan(323*pi/6) = tan((329*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(323*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(217*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_925_test (h0 : sin(4*pi/3)≠ 0) (h1 : (4*sin(4*pi/3))≠ 0) (h2 : (2*sin(4*pi/3))≠ 0) : sin(pi/3) * sin(pi)=sin(995*pi/6)/2 - sin(8*pi/3)/(4*sin(4*pi/3)):=
begin
have : cos(-2*pi/3) = sin(995*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos((-2) * pi / 3) / 2 - sin(8 * pi / 3) / (2 * sin(4 * pi / 3)) / 2 = cos(-2*pi/3)/2 - sin(8*pi/3)/(4*sin(4*pi/3)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi/3) = sin(8*pi/3) / ( 2 * sin(4*pi/3) ),
{
have : sin(8*pi/3) = sin(2*(4*pi/3)),
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
have : sin(pi/3) * sin(pi) = cos(-2*pi/3) / 2 - cos(4*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((pi/3) + (pi)) = cos(4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (pi)) = cos(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_926_test : sin(2*pi)=-cos(263*pi/2)/2 - cos(-pi/2)*cos(132*pi) + cos(-265*pi/2)/2:=
begin
have : cos((-265) * pi / 2) / 2 - cos(263 * pi / 2) / 2 - cos(-pi / 2) * cos(132 * pi) = -cos(263*pi/2)/2 - cos(-pi/2)*cos(132*pi) + cos(-265*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) * sin(132*pi) = cos(-265*pi/2) / 2 - cos(263*pi/2) / 2,
{
rw sin_mul_sin,
have : cos((-pi/2) + (132*pi)) = cos(263*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (132*pi)) = cos(-265*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (sin(-pi/2) * sin(132*pi)) = sin(-pi/2)*sin(132*pi),
{
ring,
},
have : -(-sin(132 * pi) * sin(-pi / 2) + cos(132 * pi) * cos(-pi / 2)) = sin(-pi/2)*sin(132*pi) - cos(-pi/2)*cos(132*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(263*pi/2) = -sin(132*pi) * sin(-pi/2) + cos(132*pi) * cos(-pi/2),
{
have : cos(263*pi/2) = cos((132*pi) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = - cos(263*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_927_test : -sin(pi/6)*cos(62*pi) + cos(-pi/2)*cos(pi/6)=- 1 / 2:=
begin
have : -cos(62 * pi) * sin(pi / 6) + cos(-pi / 2) * cos(pi / 6) = -sin(pi/6)*cos(62*pi) + cos(-pi/2)*cos(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(62*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_928_test : sin(-pi/6) + sin(pi/3)=(-2 + 4*cos(1191*pi/8)**2)*sin(pi/12):=
begin
have : 2 * (-1 + 2 * (-cos(1191 * pi / 8)) ** 2) * sin(pi / 12) = (-2 + 4*cos(1191*pi/8)**2)*sin(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/8) = -cos(1191*pi/8),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/8) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin(pi / 12) * (2 * cos(-pi / 8) ** 2 - 1) = 2*(-1 + 2*cos(-pi/8)**2)*sin(pi/12),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(-pi/6) + sin(pi/3) = 2 * sin(pi/12) * cos(-pi/4),
{
rw sin_add_sin,
have : sin(((-pi/6) + (pi/3))/2) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-pi/6) - (pi/3))/2) = cos(-pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_929_test : sin(11*pi/6)*sin(217*pi/2) - sin(2*pi)*cos(11*pi/6)=sin(1163*pi/6):=
begin
have : cos(2*pi) = sin(217*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (53),
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
have : sin(-pi/6) = sin(1163*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/6) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_930_test : sin(-45*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -sin((-45) * pi / 4) = sin(-45*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(651*pi/4) = -sin(-45*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (651*pi/4) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(651*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/4) (81),
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


lemma Trigo_931_test : -cos(-31*pi)=1:=
begin
have : -cos((-31) * pi) = -cos(-31*pi),
{
field_simp at *,
},
have : sin(91*pi/2) = cos(-31*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (91*pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(91*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (22),
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


lemma Trigo_932_test : (1 - 2*sin(pi/6)**2)*sin(-pi/12) + sin(pi/3)*cos(-pi/12)=sqrt( 2 ) / 2:=
begin
have : sin(-pi / 12) * (1 - 2 * sin(pi / 6) ** 2) + sin(pi / 3) * cos(-pi / 12) = (1 - 2*sin(pi/6)**2)*sin(-pi/12) + sin(pi/3)*cos(-pi/12),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(-pi/12) * cos(pi/3) + sin(pi/3) * cos(-pi/12),
{
have : sin(pi/4) = sin((-pi/12) + (pi/3)),
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


lemma Trigo_933_test (h0 : cos(pi/6)≠ 0) (h1 : (1-tan(pi/6)**2)≠ 0) (h2 : cos((pi/3)/2)≠ 0) (h3 : ((-(1-cos(pi/3))**2/sin(pi/3)**2+1)*sin(pi/3))≠ 0) (h4 : (1-((1-cos(pi/3))/sin(pi/3))**2)≠ 0) (h5 : sin(pi/3)≠ 0) : 2*(1 - cos(pi/3))/((-(1 - cos(pi/3))**2/sin(pi/3)**2 + 1)*sin(pi/3))=- 1 / tan(437*pi/6):=
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
have : tan(pi/3) = - 1 / tan(437*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_934_test : -sin(289*pi/2)*cos(198*pi)=- sin(5*pi/2) / 2 + sin(3*pi/2) / 2:=
begin
have : -cos(198 * pi) * sin(289 * pi / 2) = -sin(289*pi/2)*cos(198*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -cos(198*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/2) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(289*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(2*pi) = - sin(5*pi/2) / 2 + sin(3*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((2*pi) + (-pi/2)) = sin(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (-pi/2)) = sin(5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_935_test : (-sin(pi/6)*cos(428*pi/3) + sin(428*pi/3)*cos(pi/6))**2=1 - sin(2*pi) ** 2:=
begin
have : (sin(428 * pi / 3) * cos(pi / 6) - sin(pi / 6) * cos(428 * pi / 3)) ** 2 = (-sin(pi/6)*cos(428*pi/3) + sin(428*pi/3)*cos(pi/6))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(285*pi/2) = sin(428*pi/3) * cos(pi/6) - sin(pi/6) * cos(428*pi/3),
{
have : sin(285*pi/2) = sin((428*pi/3) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(285*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (72),
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


lemma Trigo_936_test : sin(572*pi/3)=-sin(-2*pi)*sin(-pi/6) + cos(-13*pi/6)/2 + cos(11*pi/6)/2:=
begin
have : cos(-13*pi/6) = sin(572*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-13*pi/6) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-2) * pi) * sin(-pi / 6) + (cos(11 * pi / 6) / 2 + cos((-13) * pi / 6) / 2) = -sin(-2*pi)*sin(-pi/6) + cos(-13*pi/6)/2 + cos(11*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) * cos(-2*pi) = cos(11*pi/6) / 2 + cos(-13*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (-2*pi)) = cos(-13*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (-2*pi)) = cos(11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : (cos(-pi/6) * cos(-2*pi)) = cos(-2*pi)*cos(-pi/6),
{
ring,
},
conv {to_rhs, rw this,},
have : cos(-13*pi/6) = - sin(-2*pi) * sin(-pi/6) + cos(-2*pi) * cos(-pi/6),
{
have : cos(-13*pi/6) = cos((-2*pi) + (-pi/6)),
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


lemma Trigo_937_test : cos(259*pi/6)/2 + cos(265*pi/6)/2=cos(-5*pi/6) / 2 + cos(pi/6) / 2:=
begin
have : cos(131*pi/3) * cos(pi/2) = cos(259*pi/6) / 2 + cos(265*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((131*pi/3) + (pi/2)) = cos(265*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((131*pi/3) - (pi/2)) = cos(259*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(131*pi/3) * cos(pi/2)) = cos(pi/2)*cos(131*pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(131 * pi / 3) * cos(pi / 2) = cos(pi/2)*cos(131*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = cos(131*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) * cos(pi/2) = cos(-5*pi/6) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
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


lemma Trigo_938_test : cos(205*pi)=4 * cos(-pi/3) ** 3 - 3 * cos(-pi/3):=
begin
have : - -cos(205 * pi) = cos(205*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(205*pi/2) = -cos(205*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (205*pi/2) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(205*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (51),
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


lemma Trigo_939_test : -cos(382*pi/3)=sin(349*pi/6):=
begin
have : cos(47*pi/3) = -cos(382*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (47*pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(47*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(349*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_940_test (h0 : sin(1177*pi/6)≠ 0) (h1 : (2*sin(1177*pi/6))≠ 0) : sin(1177*pi/3)*cos(pi/3)/(2*sin(1177*pi/6))=cos(-pi/2) / 2 + cos(pi/6) / 2:=
begin
have : cos(pi / 3) * (sin(1177 * pi / 3) / (2 * sin(1177 * pi / 6))) = sin(1177*pi/3)*cos(pi/3)/(2*sin(1177*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1177*pi/6) = sin(1177*pi/3) / ( 2 * sin(1177*pi/6) ),
{
have : sin(1177*pi/3) = sin(2*(1177*pi/6)),
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
have : cos(1177 * pi / 6) * cos(pi / 3) = cos(pi/3)*cos(1177*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) = cos(1177*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/6) * cos(pi/3) = cos(-pi/2) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi/6) + (pi/3)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (pi/3)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_941_test (h0 : sin(271*pi/3)≠ 0) (h1 : (2*sin(271*pi/3))≠ 0) (h2 : (4*sin(271*pi/3))≠ 0) : sin(-pi/3) ** 2=sin(542*pi/3)/(4*sin(271*pi/3)) + 1/2:=
begin
have : sin(542 * pi / 3) / (2 * sin(271 * pi / 3)) / 2 + 1 / 2 = sin(542*pi/3)/(4*sin(271*pi/3)) + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(271*pi/3) = sin(542*pi/3) / ( 2 * sin(271*pi/3) ),
{
have : sin(542*pi/3) = sin(2*(271*pi/3)),
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
have : 1 / 2 - -cos(271 * pi / 3) / 2 = cos(271*pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi/3) = -cos(271*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/3) (45),
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


lemma Trigo_942_test : -sin(322*pi/3)=-2*sin(47*pi/6)*cos(47*pi/6):=
begin
have : cos(-pi/6) = -sin(322*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(2 * sin(47 * pi / 6) * cos(47 * pi / 6)) = -2*sin(47*pi/6)*cos(47*pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(47*pi/3) = 2 * sin(47*pi/6) * cos(47*pi/6),
{
have : sin(47*pi/3) = sin(2*(47*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/6) = - sin(47*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_943_test : 1 - 2*sin(203*pi/3)**2=cos(278*pi/3):=
begin
have : cos(406*pi/3) = 1 - 2 * sin(203*pi/3) ** 2,
{
have : cos(406*pi/3) = cos(2*(203*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(406*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(278*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_944_test : -cos(131*pi/2)=sin(175*pi):=
begin
have : cos(257*pi/2) = cos(131*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (257*pi/2) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(257*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(175*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_945_test : -sin(217*pi)=sin(127*pi):=
begin
have : sin(152*pi) = -sin(217*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (152*pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(152*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(127*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-2*pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_946_test : cos(43*pi/2)=- sin(173*pi):=
begin
have : sin(39*pi) = cos(43*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (39*pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(39*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = - sin(173*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_947_test (h0 : cos(49*pi/4)≠ 0) : sin(49*pi/4)/cos(49*pi/4)=1:=
begin
have : tan(49*pi/4) = sin(49*pi/4) / cos(49*pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_948_test : -cos(-103*pi/2)=- 4 * sin(pi/3) ** 3 + 3 * sin(pi/3):=
begin
have : -cos((-103) * pi / 2) = -cos(-103*pi/2),
{
field_simp at *,
},
have : cos(117*pi/2) = -cos(-103*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (117*pi/2) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = cos(117*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (28),
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


lemma Trigo_949_test : cos(170*pi)=-sin(187*pi/2):=
begin
have : cos(-2*pi) = cos(170*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(157*pi/2) = -sin(187*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (157*pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = sin(157*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-2*pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_950_test : -2*sin(-pi/2)**2 + 2*sin(-pi/6)**2=- 2 * sin(-pi/3) * sin(-2*pi/3):=
begin
have : -1 + (1 - 2 * sin(-pi / 2) ** 2) + 2 * sin(-pi / 6) ** 2 = -2*sin(-pi/2)**2 + 2*sin(-pi/6)**2,
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
have : cos(-pi) - (1 - 2 * sin(-pi / 6) ** 2) = -1 + cos(-pi) + 2*sin(-pi/6)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : cos(-pi) - cos(-pi/3) = - 2 * sin(-pi/3) * sin(-2*pi/3),
{
rw cos_sub_cos,
have : sin(((-pi) + (-pi/3))/2) = sin(-2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((-pi) - (-pi/3))/2) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_951_test : -cos(-209*pi/3)=- 1 / 2:=
begin
have : -cos((-209) * pi / 3) = -cos(-209*pi/3),
{
field_simp at *,
},
have : sin(499*pi/6) = -cos(-209*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (499*pi/6) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(499*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (41),
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


lemma Trigo_952_test : sin(603*pi/4)=sqrt( 2 ) / 2:=
begin
have : - -sin(603 * pi / 4) = sin(603*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(157*pi/4) = -sin(603*pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (157*pi/4) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -sin(157*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/4) (19),
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


lemma Trigo_953_test (h0 : cos(pi/3)≠ 0) (h1 : cos((2*pi/3)/2)≠ 0) (h2 : sin(2*pi/3)≠ 0) : (-4*sin(pi/9)**3 + 3*sin(pi/9))/cos(pi/3)=(1 - cos(2*pi/3))/sin(2*pi/3):=
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
conv {to_rhs, rw ← this,},
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
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_954_test (h0 : tan(449*pi/12)≠ 0) (h1 : -tan(115*pi/12)≠ 0) (h2 : tan(115*pi/12)≠ 0) : -1/tan(115*pi/12)=2 - sqrt( 3 ):=
begin
have : 1 / -tan(115 * pi / 12) = -1/tan(115*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(449*pi/12) = -tan(115*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (449*pi/12) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 1 / tan(449*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (37),
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


lemma Trigo_955_test : 1 - 2*(3*sin(-pi/12) - 4*sin(-pi/12)**3)**2=- cos(335*pi/2):=
begin
have : 1 - 2 * ((-4) * sin(-pi / 12) ** 3 + 3 * sin(-pi / 12)) ** 2 = 1 - 2*(3*sin(-pi/12) - 4*sin(-pi/12)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -4 * sin(-pi/12) ** 3 + 3 * sin(-pi/12),
{
have : sin(-pi/4) = sin(3*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
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
have : cos(-pi/2) = - cos(335*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi/2) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_956_test : -sin(-48*pi)=cos(47*pi/2):=
begin
have : -sin((-48) * pi) = -sin(-48*pi),
{
field_simp at *,
},
have : cos(189*pi/2) = sin(-48*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (189*pi/2) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(189*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = cos(47*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_957_test : 2*sin(pi/4)*cos(pi/4)=-cos(185*pi):=
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
have : cos(44*pi) = -cos(185*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (44*pi) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = cos(44*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_958_test (h0 : cos((-pi/3)/2)≠ 0) (h1 : (cos(-pi/3)+1)≠ 0) (h2 : (1+cos(-pi/3))≠ 0) (h3 : tan(163*pi/3)≠ 0) (h4 : -tan(163*pi/3)≠ 0) : sin(-pi/3)/(cos(-pi/3) + 1)=-1/tan(163*pi/3):=
begin
have : 1 / -tan(163 * pi / 3) = -1/tan(163*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(53*pi/3) = -tan(163*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (53*pi/3) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : tan(-pi/6) = 1 / tan(53*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/6) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_959_test (h0 : cos((3*pi/2)/2)≠ 0) (h1 : sin(3*pi/2)≠ 0) (h2 : cos(134*pi)≠ 0) (h3 : -cos(134*pi)≠ 0) : -(1 - cos(3*pi/2))/cos(134*pi)=- 1:=
begin
have : (1 - cos(3 * pi / 2)) / -cos(134 * pi) = -(1 - cos(3*pi/2))/cos(134*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/2) = -cos(134*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/2) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_960_test : cos(-2*pi)=-sin(571*pi/2):=
begin
have : sin(283*pi/2) = sin(571*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (283*pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(151*pi/2) = sin(283*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (151*pi/2) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-2*pi) = - sin(151*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2*pi) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_961_test (h0 : cos(pi/6)≠ 0) (h1 : (2*cos(pi/6))≠ 0) : sin(pi/3)/(2*cos(pi/6))=-sin(959*pi/6):=
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
have : cos(334*pi/3) = sin(959*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (334*pi/3) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/6) = - cos(334*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_963_test (h0 : tan(295*pi/6)≠ 0) (h1 : cos(295*pi/6)≠ 0) (h2 : (sin(295*pi/6)/cos(295*pi/6))≠ 0) (h3 : sin(295*pi/6)≠ 0) : -cos(295*pi/6)/sin(295*pi/6)=tan(221*pi/3):=
begin
have : (-1) / (sin(295 * pi / 6) / cos(295 * pi / 6)) = -cos(295*pi/6)/sin(295*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(295*pi/6) = sin(295*pi/6) / cos(295*pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = tan(221*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (-pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_964_test : -sin(325*pi/2) + sin(-pi)=-2*sin(-3*pi/4)*sin(87*pi/4):=
begin
have : sin(-pi) + -sin(325 * pi / 2) = -sin(325*pi/2) + sin(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = -sin(325*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/2) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin((-3) * pi / 4) * -sin(87 * pi / 4) = -2*sin(-3*pi/4)*sin(87*pi/4),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/4) = -sin(87*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/4) (10),
focus{repeat {apply congr_arg _}},
simp,
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


lemma Trigo_965_test : (sin(pi/2)*cos(308*pi/3) + sin(308*pi/3)*cos(pi/2))*cos(pi/3)=- sin(pi/2) / 2 + sin(pi/6) / 2:=
begin
have : (sin(308 * pi / 3) * cos(pi / 2) + sin(pi / 2) * cos(308 * pi / 3)) * cos(pi / 3) = (sin(pi/2)*cos(308*pi/3) + sin(308*pi/3)*cos(pi/2))*cos(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(619*pi/6) = sin(308*pi/3) * cos(pi/2) + sin(pi/2) * cos(308*pi/3),
{
have : sin(619*pi/6) = sin((308*pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(619*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/6) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * cos(pi/3) = - sin(pi/2) / 2 + sin(pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (-pi/6)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (-pi/6)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
end


lemma Trigo_966_test : -1 + 2*cos(507*pi/4)**2=0:=
begin
have : -1 + 2 * (-cos(507 * pi / 4)) ** 2 = -1 + 2*cos(507*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -cos(507*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/4) (63),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi/2) = 0,
{
rw cos_pi_div_two,
},
rw this,
end


lemma Trigo_967_test : cos(735*pi/4)=sqrt( 2 ) / 2:=
begin
have : cos(407*pi/4) = cos(735*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (407*pi/4) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(407*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (50),
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


lemma Trigo_968_test : 1 - 2*sin(87*pi/2)**2=cos(97*pi):=
begin
have : cos(87*pi) = 1 - 2 * sin(87*pi/2) ** 2,
{
have : cos(87*pi) = cos(2*(87*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(87*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) = cos(97*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_969_test : (-3*cos(4*pi/9) + 4*cos(4*pi/9)**3)*sin(-pi) + sin(4*pi/3)*cos(-pi)=sqrt( 3 ) / 2:=
begin
have : sin(-pi) * (4 * cos(4 * pi / 9) ** 3 - 3 * cos(4 * pi / 9)) + sin(4 * pi / 3) * cos(-pi) = (-3*cos(4*pi/9) + 4*cos(4*pi/9)**3)*sin(-pi) + sin(4*pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/3) = 4 * cos(4*pi/9) ** 3 - 3 * cos(4*pi/9),
{
have : cos(4*pi/3) = cos(3*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 3) * cos(-pi) + sin(-pi) * cos(4 * pi / 3) = sin(-pi)*cos(4*pi/3) + sin(4*pi/3)*cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(4*pi/3) * cos(-pi) + sin(-pi) * cos(4*pi/3),
{
have : sin(pi/3) = sin((4*pi/3) + (-pi)),
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


lemma Trigo_970_test : sin(pi/3)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi/3)=-sin(61*pi/3):=
begin
have : sin((-2) * pi / 3) * cos(pi / 3) + sin(pi / 3) * cos((-2) * pi / 3) = sin(pi/3)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(-2*pi/3) * cos(pi/3) + sin(pi/3) * cos(-2*pi/3),
{
have : sin(-pi/3) = sin((-2*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(649*pi/6) = sin(61*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (649*pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/3) = - cos(649*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/3) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_971_test : -sin(191*pi/12)**2 + cos(191*pi/12)**2=sqrt( 3 ) / 2:=
begin
have : cos(191*pi/6) = -sin(191*pi/12) ** 2 + cos(191*pi/12) ** 2,
{
have : cos(191*pi/6) = cos(2*(191*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(191*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (16),
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


lemma Trigo_972_test (h0 : cos(pi/3)≠ 0) (h1 : cos(4*pi/3)≠ 0) (h2 : cos(pi)≠ 0) (h3 : (tan(pi)*tan(4*pi/3)+1)≠ 0) (h4 : (1+tan(4*pi/3)*tan(pi))≠ 0) : sin(518*pi/3)/cos(pi/3)=(-tan(pi) + tan(4*pi/3))/(tan(pi)*tan(4*pi/3) + 1):=
begin
have : (tan(4 * pi / 3) - tan(pi)) / (1 + tan(4 * pi / 3) * tan(pi)) = (-tan(pi) + tan(4*pi/3))/(tan(pi)*tan(4*pi/3) + 1),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(pi/3) = ( tan(4*pi/3) - tan(pi) ) / ( 1 + tan(4*pi/3) * tan(pi) ),
{
have : tan(pi/3) = tan((4*pi/3) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : sin(pi/3) = sin(518*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) / cos(pi/3) = tan(pi/3),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_973_test : -sin(48*pi)=-sin(320*pi):=
begin
have : cos(315*pi/2) = sin(320*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (315*pi/2) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-pi/2) = -sin(48*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (23),
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


lemma Trigo_974_test (h0 : cos(859*pi/6)≠ 0) (h1 : (2*cos(859*pi/6))≠ 0) : -sin(859*pi/3)/(2*cos(859*pi/6))=- cos(28*pi/3):=
begin
have : -(sin(859 * pi / 3) / (2 * cos(859 * pi / 6))) = -sin(859*pi/3)/(2*cos(859*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(859*pi/6) = sin(859*pi/3) / ( 2 * cos(859*pi/6) ),
{
have : sin(859*pi/3) = sin(2*(859*pi/6)),
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
have : cos(pi/3) = -sin(859*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = - cos(28*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_975_test : sin(115*pi/2)=-1 + 2*cos(-pi/2)**2:=
begin
have : cos(-pi) = sin(115*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - cos(-pi / 2) ** 2) + cos(-pi / 2) ** 2 = -1 + 2*cos(-pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) ** 2 = 1 - cos(-pi/2) ** 2,
{
rw sin_sq,
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


lemma Trigo_976_test (h0 : tan(1013*pi/12)≠ 0) (h1 : -tan((-953)*pi/12)≠ 0) (h2 : tan(-953*pi/12)≠ 0) : -1/tan(-953*pi/12)=2 - sqrt( 3 ):=
begin
have : 1 / -tan((-953) * pi / 12) = -1/tan(-953*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1013*pi/12) = -tan(-953*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (1013*pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = 1 / tan(1013*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/12) (84),
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


lemma Trigo_977_test (h0 : tan(130*pi/3)≠ 0) (h1 : tan(755*pi/6)≠ 0) (h2 : ((-1)/tan(755*pi/6))≠ 0) : -tan(755*pi/6)=sqrt( 3 ) / 3:=
begin
have : 1 / ((-1) / tan(755 * pi / 6)) = -tan(755*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(130*pi/3) = -1 / tan(755*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (130*pi/3) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(130*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (43),
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


lemma Trigo_978_test : sin(5*pi/6)=(-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(pi) + (-sin(pi/2)**2 + cos(pi/2)**2)*sin(-pi/6):=
begin
have : (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) * sin(pi) + sin(-pi / 6) * (-sin(pi / 2) ** 2 + cos(pi / 2) ** 2) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(pi) + (-sin(pi/2)**2 + cos(pi/2)**2)*sin(-pi/6),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : sin(pi) * (-sin(-pi / 12) ** 2 + cos(-pi / 12) ** 2) + sin(-pi / 6) * cos(pi) = (-sin(-pi/12)**2 + cos(-pi/12)**2)*sin(pi) + sin(-pi/6)*cos(pi),
{
field_simp at *,
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
have : sin(5*pi/6) = sin(pi) * cos(-pi/6) + sin(-pi/6) * cos(pi),
{
have : sin(5*pi/6) = sin((pi) + (-pi/6)),
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


lemma Trigo_979_test : 1 - 2*sin(-pi/6)**2=-4*sin(-pi/12)**2*cos(-pi/12)**2 + cos(-pi/6)**2:=
begin
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
conv {to_lhs, rw ← this,},
have : -(2 * sin(-pi / 12) * cos(-pi / 12)) ** 2 + cos(-pi / 6) ** 2 = -4*sin(-pi/12)**2*cos(-pi/12)**2 + cos(-pi/6)**2,
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


lemma Trigo_980_test : cos(-2*pi)*cos(413*pi/4) + sin(-2*pi)*sin(413*pi/4)=- sqrt( 2 ) / 2:=
begin
have : sin(413 * pi / 4) * sin((-2) * pi) + cos(413 * pi / 4) * cos((-2) * pi) = cos(-2*pi)*cos(413*pi/4) + sin(-2*pi)*sin(413*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(421*pi/4) = sin(413*pi/4) * sin(-2*pi) + cos(413*pi/4) * cos(-2*pi),
{
have : cos(421*pi/4) = cos((413*pi/4) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = cos(421*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (3*pi/4) (53),
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


lemma Trigo_981_test (h0 : cos((pi)/2)≠ 0) (h1 : sin(pi)≠ 0) (h2 : tan(45*pi)≠ 0) : (1 - cos(pi))/sin(pi)=-1/tan(45*pi):=
begin
have : (-1) / tan(45 * pi) = -1/tan(45*pi),
{
field_simp at *,
},
have : tan(75*pi/2) = -1 / tan(45*pi),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (75*pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
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
have : tan(pi/2) = tan(75*pi/2),
{
rw tan_eq_tan_add_int_mul_pi (pi/2) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_982_test : cos(-pi/2)/2 + cos(pi/6)/2 + cos(-pi/3)*cos(-pi/6)=2 * cos(pi/3) * cos(-pi/6):=
begin
have : -(cos(pi / 6) / 2 - cos(-pi / 2) / 2) + cos(-pi / 3) * cos(-pi / 6) + cos(pi / 6) = cos(-pi/2)/2 + cos(pi/6)/2 + cos(-pi/3)*cos(-pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) * sin(-pi/3) = cos(pi/6) / 2 - cos(-pi/2) / 2,
{
rw sin_mul_sin,
have : cos((-pi/6) + (-pi/3)) = cos(-pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/6) - (-pi/3)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(-pi/6) * sin(-pi/3)) = -sin(-pi/3)*sin(-pi/6),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi / 6) + (-sin(-pi / 3) * sin(-pi / 6) + cos(-pi / 3) * cos(-pi / 6)) = -sin(-pi/3)*sin(-pi/6) + cos(-pi/3)*cos(-pi/6) + cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -sin(-pi/3) * sin(-pi/6) + cos(-pi/3) * cos(-pi/6),
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


lemma Trigo_983_test : -(cos(2*pi)*cos(137*pi/2) - sin(2*pi)*sin(137*pi/2))*cos(pi/3)=cos(-5*pi/6) / 2 + cos(-pi/6) / 2:=
begin
have : -cos(pi / 3) * (-sin(137 * pi / 2) * sin(2 * pi) + cos(137 * pi / 2) * cos(2 * pi)) = -(cos(2*pi)*cos(137*pi/2) - sin(2*pi)*sin(137*pi/2))*cos(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(141*pi/2) = -sin(137*pi/2) * sin(2*pi) + cos(137*pi/2) * cos(2*pi),
{
have : cos(141*pi/2) = cos((137*pi/2) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(141 * pi / 2) * cos(pi / 3) = -cos(pi/3)*cos(141*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) = -cos(141*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/2) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/2) * cos(pi/3) = cos(-5*pi/6) / 2 + cos(-pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-pi/2) + (pi/3)) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi/2) - (pi/3)) = cos(-5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_984_test (h0 : cos(-7*pi/4)≠ 0) (h1 : cos(-2*pi)≠ 0) (h2 : (1+tan((-7)*pi/4)*tan((-2)*pi))≠ 0) (h3 : (tan(-2*pi)*tan(-7*pi/4)+1)≠ 0) (h4 : (tan((-2)*pi)*-tan(155*pi/4)+1)≠ 0) (h5 : (-tan(-2*pi)*tan(155*pi/4)+1)≠ 0) : (-tan(-2*pi) - tan(155*pi/4))/(-tan(-2*pi)*tan(155*pi/4) + 1)=1:=
begin
have : (-tan((-2) * pi) + -tan(155 * pi / 4)) / (tan((-2) * pi) * -tan(155 * pi / 4) + 1) = (-tan(-2*pi) - tan(155*pi/4))/(-tan(-2*pi)*tan(155*pi/4) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-7*pi/4) = -tan(155*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-7*pi/4) (37),
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


lemma Trigo_985_test : -3 + 4*(1 - 2*sin(-pi/6)**2)**3 + 6*sin(-pi/6)**2=- sin(385*pi/2):=
begin
have : (-3) * (1 - 2 * sin(-pi / 6) ** 2) + 4 * (1 - 2 * sin(-pi / 6) ** 2) ** 3 = -3 + 4*(1 - 2*sin(-pi/6)**2)**3 + 6*sin(-pi/6)**2,
{
field_simp at *,
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
have : cos(-pi) = - sin(385*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_986_test : tan(379*pi/6)=sqrt( 3 ) / 3:=
begin
have : - -tan(379 * pi / 6) = tan(379*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(167*pi/6) = -tan(379*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (167*pi/6) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = -tan(167*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/6) (28),
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




lemma Trigo_988_test : cos(102*pi)=cos(356*pi):=
begin
have : cos(2*pi) = cos(102*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos(356 * pi) = cos(356*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(327*pi/2) = -cos(356*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (327*pi/2) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*pi) = - sin(327*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_989_test (h0 : cos(pi/8)≠ 0) (h1 : (1-tan(pi/8)**2)≠ 0) (h2 : (1-tan(257*pi/8)**2)≠ 0) : 2*tan(257*pi/8)/(1 - tan(257*pi/8)**2)=1:=
begin
have : tan(pi/8) = tan(257*pi/8),
{
rw tan_eq_tan_add_int_mul_pi (pi/8) (32),
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


lemma Trigo_990_test : -sin(899*pi/6)=- cos(16*pi/3):=
begin
have : cos(187*pi/3) = -sin(899*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (187*pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(187*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = - cos(16*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_991_test : cos(-pi)=cos(-2*pi)*cos(-pi) + sin(-2*pi)*cos(381*pi/2):=
begin
have : cos(381 * pi / 2) * sin((-2) * pi) + cos(-pi) * cos((-2) * pi) = cos(-2*pi)*cos(-pi) + sin(-2*pi)*cos(381*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = cos(381*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(pi) = cos(-pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi) (0),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(-pi) * sin(-2*pi) + cos(-pi) * cos(-2*pi),
{
have : cos(pi) = cos((-pi) - (-2*pi)),
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


lemma Trigo_992_test : -sin(41*pi)*cos(-pi)=sin(3*pi) / 2 + sin(pi) / 2:=
begin
have : sin(142*pi) = sin(41*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (142*pi) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) = -sin(142*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi) * cos(-pi) = sin(3*pi) / 2 + sin(pi) / 2,
{
rw sin_mul_cos,
have : sin((2*pi) + (-pi)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi) - (-pi)) = sin(3*pi),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
end


lemma Trigo_993_test : cos(35*pi/2)=sin(0) + sin(-4*pi):=
begin
have : sin(-4*pi) = cos(35*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-4*pi) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sin(0) / 2 + sin((-4) * pi) / 2) = sin(0) + sin(-4*pi),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-2*pi) * cos(-2*pi) = sin(0) / 2 + sin(-4*pi) / 2,
{
rw sin_mul_cos,
have : sin((-2*pi) + (-2*pi)) = sin(-4*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-2*pi)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_rhs, rw ← this,},
have : 2*(sin(-2*pi) * cos(-2*pi)) = 2*sin(-2*pi)*cos(-2*pi),
{
ring,
},
conv {to_rhs, rw this,},
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


lemma Trigo_994_test : cos(307*pi)=sin(223*pi/2):=
begin
have : cos(109*pi) = cos(307*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (109*pi) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(109*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(223*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_995_test : cos(pi/3)=-1 + 2*(-1 + 2*cos(pi/12)**2)**2:=
begin
have : -1 + 2 * (2 * cos(pi / 12) ** 2 - 1) ** 2 = -1 + 2*(-1 + 2*cos(pi/12)**2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
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


lemma Trigo_996_test : -cos(833*pi/6)=sqrt( 3 ) / 2:=
begin
have : cos(383*pi/6) = -cos(833*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (383*pi/6) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(383*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (32),
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


lemma Trigo_997_test : sin(-17*pi/2)=- cos(114*pi):=
begin
have : sin((-17) * pi / 2) = sin(-17*pi/2),
{
field_simp at *,
},
have : sin(75*pi/2) = sin(-17*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (75*pi/2) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = sin(75*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = - cos(114*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-pi) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_998_test (h0 : cos(-pi/6)≠ 0) (h1 : (2*cos(-pi/6)**2)≠ 0) (h2 : (2*cos(-pi/6))≠ 0) (h3 : cos(-pi/6)≠ 0) (h4 : (2*sin(355*pi/3)**2)≠ 0) : tan(-pi/6)=sin(-pi/3)/(2*sin(355*pi/3)**2):=
begin
have : cos(-pi/6) = sin(355*pi/3),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/6) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi / 3) / (2 * cos(-pi / 6)) / cos(-pi / 6) = sin(-pi/3)/(2*cos(-pi/6)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
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
conv {to_rhs, rw ← this,},
have : tan(-pi/6) = sin(-pi/6) / cos(-pi/6),
{
rw tan_eq_sin_div_cos,
},
rw this,
end


lemma Trigo_999_test : sin(pi/2)*cos(-pi) + sin(-pi)*cos(pi/2)=-sin(-243*pi/2):=
begin
have : sin(-pi/2) = sin(pi/2) * cos(-pi) + sin(-pi) * cos(pi/2),
{
have : sin(-pi/2) = sin((pi/2) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-243) * pi / 2) = -sin(-243*pi/2),
{
field_simp at *,
},
have : cos(163*pi) = -sin(-243*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (163*pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/2) = cos(163*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/2) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1000_test : -cos(277*pi/2)=-2*cos(2*pi)*cos(329*pi/2):=
begin
have : 2 * -cos(329 * pi / 2) * cos(2 * pi) = -2*cos(2*pi)*cos(329*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : sin(2*pi) = -cos(329*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(4*pi) = -cos(277*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (4*pi) (67),
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


lemma Trigo_1001_test : -cos(677*pi/6)=sqrt( 3 ) / 2:=
begin
have : sin(286*pi/3) = cos(677*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (286*pi/3) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_1002_test : (-1 + 2*cos(91*pi/4)**2)**2=cos(pi) / 2 + 1 / 2:=
begin
have : (2 * cos(91 * pi / 4) ** 2 - 1) ** 2 = (-1 + 2*cos(91*pi/4)**2)**2,
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(91*pi/2) = 2 * cos(91*pi/4) ** 2 - 1,
{
have : cos(91*pi/2) = cos(2*(91*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(91*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (23),
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


lemma Trigo_1003_test : -cos(-pi/3)*cos(2165*pi/12) - sin(-pi/3)*sin(2165*pi/12)=sqrt( 2 ) / 2:=
begin
have : -(sin(2165 * pi / 12) * sin(-pi / 3) + cos(2165 * pi / 12) * cos(-pi / 3)) = -cos(-pi/3)*cos(2165*pi/12) - sin(-pi/3)*sin(2165*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(723*pi/4) = sin(2165*pi/12) * sin(-pi/3) + cos(2165*pi/12) * cos(-pi/3),
{
have : cos(723*pi/4) = cos((2165*pi/12) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = -cos(723*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (90),
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




lemma Trigo_1005_test : cos(0)*cos(-pi) + sin(0)*sin(-pi)=-1/2 + cos(pi)/2 + cos(pi/2)**2:=
begin
have : sin(0) * sin(-pi) + cos(0) * cos(-pi) = cos(0)*cos(-pi) + sin(0)*sin(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(0) * sin(-pi) + cos(0) * cos(-pi),
{
have : cos(pi) = cos((0) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 / 2 - cos(pi) / 2) + cos(pi / 2) ** 2 = -1/2 + cos(pi)/2 + cos(pi/2)**2,
{
field_simp at *,
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


lemma Trigo_1006_test : -sin(119*pi/2)=-sin(383*pi/2):=
begin
have : sin(pi/2) = -sin(119*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/2) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(173*pi) = sin(383*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (173*pi) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = - cos(173*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1008_test : -cos(269*pi/2)=-4*sin(77*pi)**3 + 3*sin(77*pi):=
begin
have : (-4) * sin(77 * pi) ** 3 + 3 * sin(77 * pi) = -4*sin(77*pi)**3 + 3*sin(77*pi),
{
field_simp at *,
},
have : sin(pi) = sin(77*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(3*pi) = -cos(269*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi) (68),
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


lemma Trigo_1009_test : -cos(737*pi/12)=- sqrt( 2 ) / 4 + sqrt( 6 ) / 4:=
begin
have : cos(689*pi/12) = cos(737*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (689*pi/12) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(689*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (28),
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


lemma Trigo_1010_test : sin(566*pi/3)=-(1 - 2*sin(-pi/6)**2)*sin(-pi) + sin(-pi/3)*cos(-pi):=
begin
have : sin(2*pi/3) = sin(566*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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


lemma Trigo_1011_test (h0 : cos(-pi)≠ 0) : -(cos(2*pi)*cos(351*pi/2) + sin(2*pi)*sin(351*pi/2))/cos(-pi)=tan(-pi):=
begin
have : -(sin(351 * pi / 2) * sin(2 * pi) + cos(351 * pi / 2) * cos(2 * pi)) / cos(-pi) = -(cos(2*pi)*cos(351*pi/2) + sin(2*pi)*sin(351*pi/2))/cos(-pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(347*pi/2) = sin(351*pi/2) * sin(2*pi) + cos(351*pi/2) * cos(2*pi),
{
have : cos(347*pi/2) = cos((351*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -cos(347*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi) (87),
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


lemma Trigo_1012_test : -cos(388*pi/3)=sin(2*pi)*cos(-pi/6) + sin(13*pi/6)/2 - sin(11*pi/6)/2:=
begin
have : sin(13*pi/6) = -cos(388*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/6) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi) * cos(-pi / 6) - (-sin(13 * pi / 6) / 2 + sin(11 * pi / 6) / 2) = sin(2*pi)*cos(-pi/6) + sin(13*pi/6)/2 - sin(11*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) * cos(2*pi) = -sin(13*pi/6) / 2 + sin(11*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
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
ring,
},
conv {to_rhs, rw ← this,},
have : (sin(-pi/6) * cos(2*pi)) = sin(-pi/6)*cos(2*pi),
{
ring,
},
have : sin(13*pi/6) = sin(2*pi) * cos(-pi/6) - sin(-pi/6) * cos(2*pi),
{
have : sin(13*pi/6) = sin((2*pi) - (-pi/6)),
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


lemma Trigo_1013_test : sin(-pi/6)=cos(68*pi/3):=
begin
have : - -cos(68 * pi / 3) = cos(68*pi/3),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(-31*pi/3) = -cos(68*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-31*pi/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -cos((-31) * pi / 3) = -cos(-31*pi/3),
{
field_simp at *,
},
have : cos(235*pi/3) = cos(-31*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (235*pi/3) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi/6) = - cos(235*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/6) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1014_test (h0 : tan(71*pi/6)≠ 0) (h1 : cos((71*pi/3)/2)≠ 0) (h2 : (1+cos(71*pi/3))≠ 0) (h3 : (sin(71*pi/3)/(1+cos(71*pi/3)))≠ 0) (h4 : sin(71*pi/3)≠ 0) : (cos(71*pi/3) + 1)/sin(71*pi/3)=- 1 / tan(145*pi/6):=
begin
have : 1 / (sin(71 * pi / 3) / (1 + cos(71 * pi / 3))) = (cos(71*pi/3) + 1)/sin(71*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(71*pi/6) = sin(71*pi/3) / ( 1 + cos(71*pi/3) ),
{
have : tan(71*pi/6) = tan((71*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = 1 / tan(71*pi/6),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-pi/3) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = - 1 / tan(145*pi/6),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (-pi/3) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end




lemma Trigo_1016_test : -cos(298*pi/3)=1 / 2:=
begin
have : sin(109*pi/6) = -cos(298*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (109*pi/6) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(109*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (9),
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


lemma Trigo_1017_test : cos(907*pi/3)=1 / 2:=
begin
have : sin(893*pi/6) = cos(907*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (893*pi/6) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(893*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (74),
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


lemma Trigo_1018_test : -sin(-3*pi/2)*sin(2*pi) - cos(2*pi)*cos(179*pi/2)=0:=
begin
have : -cos(179 * pi / 2) * cos(2 * pi) - sin((-3) * pi / 2) * sin(2 * pi) = -sin(-3*pi/2)*sin(2*pi) - cos(2*pi)*cos(179*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/2) = -cos(179*pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-3*pi/2) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-3) * pi / 2) * sin(2 * pi) + cos((-3) * pi / 2) * cos(2 * pi) = cos(-3*pi/2)*cos(2*pi) - sin(-3*pi/2)*sin(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(-3*pi/2) * sin(2*pi) + cos(-3*pi/2) * cos(2*pi),
{
have : cos(pi/2) = cos((-3*pi/2) + (2*pi)),
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


lemma Trigo_1019_test (h0 : sin(pi/6)≠ 0) (h1 : (2*sin(pi/6))≠ 0) (h2 : (2*sin(721*pi/6))≠ 0) : sin(pi/3)/(2*sin(721*pi/6))=sqrt( 3 ) / 2:=
begin
have : sin(pi/6) = sin(721*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/6) (60),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi/6) = sqrt( 3 ) / 2,
{
rw cos_pi_div_six,
},
rw this,
end


lemma Trigo_1020_test (h0 : sin(875*pi/6)≠ 0) (h1 : (2*sin(875*pi/6))≠ 0) : sin(875*pi/3)/(2*sin(875*pi/6))=sqrt( 3 ) / 2:=
begin
have : cos(875*pi/6) = sin(875*pi/3) / ( 2 * sin(875*pi/6) ),
{
have : sin(875*pi/3) = sin(2*(875*pi/6)),
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
have : sin(2*pi/3) = cos(875*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (73),
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


lemma Trigo_1021_test : -cos(55*pi)=1:=
begin
have : sin(269*pi/2) = -cos(55*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (269*pi/2) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(269*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (67),
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




lemma Trigo_1023_test : -1 - sin(335*pi/6) + 2*cos(-pi/12)**2=2 * cos(-pi/12) * cos(-pi/4):=
begin
have : -1 + -sin(335 * pi / 6) + 2 * cos(-pi / 12) ** 2 = -1 - sin(335*pi/6) + 2*cos(-pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(335*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi / 3) + (2 * cos(-pi / 12) ** 2 - 1) = -1 + cos(-pi/3) + 2*cos(-pi/12)**2,
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
have : cos(-pi/3) + cos(-pi/6) = 2 * cos(-pi/12) * cos(-pi/4),
{
rw cos_add_cos,
have : cos(((-pi/3) + (-pi/6))/2) = cos(-pi/4),
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
ring,
},
rw this,
end


lemma Trigo_1024_test : 4*sin(125*pi/3)**3 - 3*sin(125*pi/3)=sin(27*pi):=
begin
have : -((-4) * sin(125 * pi / 3) ** 3 + 3 * sin(125 * pi / 3)) = 4*sin(125*pi/3)**3 - 3*sin(125*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(125*pi) = -4 * sin(125*pi/3) ** 3 + 3 * sin(125*pi/3),
{
have : sin(125*pi) = sin(3*(125*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = -sin(125*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = sin(27*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1025_test : cos(99*pi/2)**2=1 / 2 - cos(-4*pi) / 2:=
begin
have : cos(173*pi/2) = cos(99*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (173*pi/2) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(173 * pi / 2)) ** 2 = cos(173*pi/2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = -cos(173*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-2*pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
rw this,
end


lemma Trigo_1026_test : sin(433*pi/3)=sqrt( 3 ) / 2:=
begin
have : - -sin(433 * pi / 3) = sin(433*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(94*pi/3) = -sin(433*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (94*pi/3) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(94*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*pi/3) (16),
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




lemma Trigo_1028_test : cos(-pi/6)**2=cos(-pi/3) / 2 + 1 / 2:=
begin
have : (-1 + 2 * (cos(-pi / 6) / 2 + 1 / 2)) ** 2 = cos(-pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/12) ** 2 = cos(-pi/6) / 2 + 1 / 2,
{
have : cos(-pi/6) = cos(2*(-pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * cos(-pi / 12) ** 2 - 1) ** 2 = (-1 + 2*cos(-pi/12)**2)**2,
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


lemma Trigo_1029_test : sin(130*pi)=cos(-91*pi/2):=
begin
have : - -cos((-91) * pi / 2) = cos(-91*pi/2),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(201*pi/2) = -cos(-91*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (201*pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-pi) = sin(130*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi) = - cos(201*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1030_test (h0 : cos(545*pi/4)≠ 0) (h1 : (2*cos(545*pi/4))≠ 0) : -sin(545*pi/2)/(2*cos(545*pi/4))=- sqrt( 2 ) / 2:=
begin
have : -(sin(545 * pi / 2) / (2 * cos(545 * pi / 4))) = -sin(545*pi/2)/(2*cos(545*pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(545*pi/4) = sin(545*pi/2) / ( 2 * cos(545*pi/4) ),
{
have : sin(545*pi/2) = sin(2*(545*pi/4)),
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
have : cos(3*pi/4) = -sin(545*pi/4),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (3*pi/4) (67),
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


lemma Trigo_1031_test (h0 : cos(pi/2)≠ 0) : tan(pi/2)=-cos(103*pi)/cos(pi/2):=
begin
have : sin(153*pi/2) = -cos(103*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (153*pi/2) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(153*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (38),
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


lemma Trigo_1032_test : -cos(154*pi)=sin(-pi/2)*sin(177*pi/2) + cos(-pi/2)*cos(pi/2):=
begin
have : cos(pi) = -cos(154*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(177 * pi / 2) * sin(-pi / 2) + cos(pi / 2) * cos(-pi / 2) = sin(-pi/2)*sin(177*pi/2) + cos(-pi/2)*cos(pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi/2) = sin(177*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (44),
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


lemma Trigo_1033_test : -4*cos(287*pi/18)**3 + 3*cos(287*pi/18)=sin(64*pi/3):=
begin
have : -(4 * cos(287 * pi / 18) ** 3 - 3 * cos(287 * pi / 18)) = -4*cos(287*pi/18)**3 + 3*cos(287*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(287*pi/6) = 4 * cos(287*pi/18) ** 3 - 3 * cos(287*pi/18),
{
have : cos(287*pi/6) = cos(3*(287*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -cos(287*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(64*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
rw this,
end


lemma Trigo_1034_test : -sin(193*pi/8)**2 + cos(pi/8)**2=sqrt( 2 ) / 2:=
begin
have : sin(pi/8) = sin(193*pi/8),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/8) (12),
focus{repeat {apply congr_arg _}},
simp,
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
have : cos(pi/4) = sqrt( 2 ) / 2,
{
rw cos_pi_div_four,
},
rw this,
end


lemma Trigo_1035_test : 1 - 2*sin(381*pi/4)**2=sin(pi/2) * sin(-2*pi) + cos(pi/2) * cos(-2*pi):=
begin
have : cos(381*pi/2) = 1 - 2 * sin(381*pi/4) ** 2,
{
have : cos(381*pi/2) = cos(2*(381*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/2) = cos(381*pi/2),
{
rw cos_eq_cos_add_int_mul_two_pi (5*pi/2) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/2) = sin(pi/2) * sin(-2*pi) + cos(pi/2) * cos(-2*pi),
{
have : cos(5*pi/2) = cos((pi/2) - (-2*pi)),
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