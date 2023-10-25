import trigo_import
open real
open_locale real
variables (x y : ℝ)



lemma Trigo_0_0_RLMT_extend : 3/4 - 3*(-sin(-5*pi/12)*sin(173*pi) + sin(pi/2)*cos(677*pi/12))**2/2=3*sqrt(3)/8:=
begin
have : 3 / 4 - 3 * (sin((-5) * pi / 12) * -sin(173 * pi) + sin(pi / 2) * cos(677 * pi / 12)) ** 2 / 2 = 3/4 - 3*(-sin(-5*pi/12)*sin(173*pi) + sin(pi/2)*cos(677*pi/12))**2/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = -sin(173*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/2) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 3 / 4 - 3 * (sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos(677 * pi / 12)) ** 2 / 2 = 3/4 - 3*(sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(677*pi/12))**2/2,
{
field_simp at *,
},
have : cos(-5*pi/12) = cos(677*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-5*pi/12) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 3 / 4 - 3 * (sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12)) ** 2 / 2 = 3/4 - 3*(sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12))**2/2,
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
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
rw cos_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_0_1_NBLH_extend(h0 : cos(5*pi/6) ≠ 0)  (h1 : tan(209*pi/3)≠ 0) (h2 : (1-(1/tan(209*pi/3))**2)≠ 0) (h3 : ((1-1/tan(209*pi/3)**2)*tan(209*pi/3))≠ 0) (h4 : sin(209*pi/3)≠ 0) (h5 : cos(209*pi/3)≠ 0) (h6 : (sin(209*pi/3)/cos(209*pi/3))≠ 0) (h7 : ((-cos(209*pi/3)**2/sin(209*pi/3)**2+1)*sin(209*pi/3))≠ 0) (h8 : ((1-1/(sin(209*pi/3)/cos(209*pi/3))**2)*(sin(209*pi/3)/cos(209*pi/3)))≠ 0) (h9 : ((-cos(467*pi/3)**2/sin(209*pi/3)**2+1)*sin(209*pi/3))≠ 0) : 2*cos(467*pi/3)/((-cos(467*pi/3)**2/sin(209*pi/3)**2 + 1)*sin(209*pi/3))=-sqrt(3):=
begin
have : cos(209*pi/3) = cos(467*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (209*pi/3) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 / ((1 - 1 / (sin(209 * pi / 3) / cos(209 * pi / 3)) ** 2) * (sin(209 * pi / 3) / cos(209 * pi / 3))) = 2*cos(209*pi/3)/((-cos(209*pi/3)**2/sin(209*pi/3)**2 + 1)*sin(209*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(209*pi/3) = sin(209*pi/3) / cos(209*pi/3),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : 2 * (1 / tan(209 * pi / 3)) / (1 - (1 / tan(209 * pi / 3)) ** 2) = 2/((1 - 1/tan(209*pi/3)**2)*tan(209*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/6) = 1 / tan(209*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (5*pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*tan(5*pi/6)/(1 - tan(5*pi/6)**2) = tan(5*pi/3),
{
have : tan(5*pi/3) = tan(2*(5*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
rw this,
have : tan(5*pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (5*pi/3) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_three,
end


lemma Trigo_0_2_LVJK_extend (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) (h2 : sin(pi/12)≠ 0) (h3 : (2*sin(pi/12))≠ 0) (h4 : (2*sin(pi/12)**2)≠ 0) : -cos(pi/2) + sin(62*pi/3)/(2*cos(pi/3)) + sin(pi/6)**2/(2*sin(pi/12)**2)=sqrt(3)+1:=
begin
have : -cos(pi / 2) + sin(62 * pi / 3) / (2 * cos(pi / 3)) + 2 * (sin(pi / 6) / (2 * sin(pi / 12))) ** 2 = -cos(pi/2) + sin(62*pi/3)/(2*cos(pi/3)) + sin(pi/6)**2/(2*sin(pi/12)**2),
{
field_simp at *,
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
have : sin(2*pi/3) = sin(62*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * pi / 3) / (2 * cos(pi / 3)) + 2 * cos(pi / 12) ** 2 - cos(pi / 2) = -cos(pi/2) + sin(2*pi/3)/(2*cos(pi/3)) + 2*cos(pi/12)**2,
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
rw cos_pi_div_two,
rw sin_pi_div_three,
have : cos(pi/12)**2 = cos(pi/6)/2 + 1/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_3_NRRR_extend : -cos(437*pi/3)*cos(955*pi/6) + sin(pi/3)**2=(3+sqrt(3))/4:=
begin
have : cos(58*pi/3) = -cos(437*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (58*pi/3) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos(58 * pi / 3) * cos(955 * pi / 6) + sin(pi / 3) ** 2 = cos(58*pi/3)*cos(955*pi/6) + sin(pi/3)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -cos(58*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/3) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) ** 2 + -cos(955 * pi / 6) * cos(pi / 3) = -cos(pi/3)*cos(955*pi/6) + sin(pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(955*pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/6) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw cos_pi_div_six,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_4_MQBL_extend : -sin(0)/2 - sin(359*pi/2)/2=1/2:=
begin
have : sin(343*pi/2) = sin(359*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (343*pi/2) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(0) / 2 + -sin(343 * pi / 2) / 2 = -sin(0)/2 - sin(343*pi/2)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -sin(343*pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/2) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : (sin(pi/4) * cos(pi/4)) = sin(pi/4)*cos(pi/4),
{
ring,
},
rw sin_pi_div_four,
rw cos_pi_div_four,
field_simp,
end


lemma Trigo_0_5_QTWV_extend (h0 : cos(3*pi/8)≠ 0) (h1 : (1-tan(3*pi/8)**2)≠ 0) (h2 : tan(689*pi/8)≠ 0) (h3 : ((1-1/tan(689*pi/8)**2)*tan(689*pi/8))≠ 0) (h4 : (1-(1/tan(689*pi/8))**2)≠ 0) (h5 : cos((689*pi/4)/2)≠ 0) (h6 : (sin(689*pi/4)/(1+cos(689*pi/4)))≠ 0) (h7 : ((-(cos(689*pi/4)+1)**2/sin(689*pi/4)**2+1)*sin(689*pi/4))≠ 0) (h8 : ((1-1/(sin(689*pi/4)/(1+cos(689*pi/4)))**2)*(sin(689*pi/4)/(1+cos(689*pi/4))))≠ 0) (h9 : sin(689*pi/4)≠ 0) (h10 : (1+cos(689*pi/4))≠ 0) : 2*(cos(689*pi/4) + 1)/((-(cos(689*pi/4) + 1)**2/sin(689*pi/4)**2 + 1)*sin(689*pi/4))=-1:=
begin
have : 2 / ((1 - 1 / (sin(689 * pi / 4) / (1 + cos(689 * pi / 4))) ** 2) * (sin(689 * pi / 4) / (1 + cos(689 * pi / 4)))) = 2*(cos(689*pi/4) + 1)/((-(cos(689*pi/4) + 1)**2/sin(689*pi/4)**2 + 1)*sin(689*pi/4)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(689*pi/8) = sin(689*pi/4) / ( 1 + cos(689*pi/4) ),
{
have : tan(689*pi/8) = tan((689*pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : 2 * (1 / tan(689 * pi / 8)) / (1 - (1 / tan(689 * pi / 8)) ** 2) = 2/((1 - 1/tan(689*pi/8)**2)*tan(689*pi/8)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/8) = 1 / tan(689*pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/8) (86),
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
have : tan(3*pi/4) = -tan(pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_four,
end


lemma Trigo_0_6_HTUW_extend : 3*sin(-367*pi/9) - 4*sin(-367*pi/9)**3=-sqrt(3)/2:=
begin
have : (-4) * sin((-367) * pi / 9) ** 3 + 3 * sin((-367) * pi / 9) = 3*sin(-367*pi/9) - 4*sin(-367*pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-367*pi/3) = -4 * sin(-367*pi/9) ** 3 + 3 * sin(-367*pi/9),
{
have : sin(-367*pi/3) = sin(3*(-367*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin((-367) * pi / 3) = sin(-367*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(463*pi/3) = -sin(-367*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (463*pi/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = -sin(463*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
field_simp,
end


lemma Trigo_0_7_HOEW_extend : -2*sin(709*pi/12)*cos(709*pi/12)=-1/2:=
begin
have : -(2 * sin(709 * pi / 12) * cos(709 * pi / 12)) = -2*sin(709*pi/12)*cos(709*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(709*pi/6) = 2 * sin(709*pi/12) * cos(709*pi/12),
{
have : sin(709*pi/6) = sin(2*(709*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(163*pi/6) = -sin(709*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (163*pi/6) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/6) = sin(163*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (23*pi/6) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (23*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_8_LNDY_extend : 4*(-sin(pi/2)*cos(43*pi/18) + sin(43*pi/18)*cos(pi/2))**3 - 3*sin(43*pi/18)*cos(pi/2) + 3*sin(pi/2)*cos(43*pi/18)=sqrt(3)/2:=
begin
have : 4 * (sin(43 * pi / 18) * cos(pi / 2) - sin(pi / 2) * cos(43 * pi / 18)) ** 3 - 3 * (sin(43 * pi / 18) * cos(pi / 2) - sin(pi / 2) * cos(43 * pi / 18)) = 4*(-sin(pi/2)*cos(43*pi/18) + sin(43*pi/18)*cos(pi/2))**3 - 3*sin(43*pi/18)*cos(pi/2) + 3*sin(pi/2)*cos(43*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/9) = sin(43*pi/18) * cos(pi/2) - sin(pi/2) * cos(43*pi/18),
{
have : sin(17*pi/9) = sin((43*pi/18) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -((-4) * sin(17 * pi / 9) ** 3 + 3 * sin(17 * pi / 9)) = 4*sin(17*pi/9)**3 - 3*sin(17*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/3) = -4 * sin(17*pi/9) ** 3 + 3 * sin(17*pi/9),
{
have : sin(17*pi/3) = sin(3*(17*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -sin(17*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*pi/3) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_0_9_PWSS_extend : -sin(2189*pi/12)*cos(3905*pi/12)=1/4:=
begin
have : cos(pi/12) = sin(2189*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(3905 * pi / 12) * cos(pi / 12) = -cos(pi/12)*cos(3905*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2195*pi/12) = -cos(3905*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2195*pi/12) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(2195*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_10_JCYT_extend : -(1 - cos(-y + 371*pi/2)**2)*cos(x + 355*pi/2)**2 - sin(y)**2*cos(x + 355*pi/2)**2 + sin(y)**2 + cos(x + 355*pi/2)**2=sin(y)**2:=
begin
have : -sin(y) ** 2 * cos(x + 355 * pi / 2) ** 2 + sin(y) ** 2 - (1 - cos(-y + 371 * pi / 2) ** 2) * cos(x + 355 * pi / 2) ** 2 + cos(x + 355 * pi / 2) ** 2 = -(1 - cos(-y + 371*pi/2)**2)*cos(x + 355*pi/2)**2 - sin(y)**2*cos(x + 355*pi/2)**2 + sin(y)**2 + cos(x + 355*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-y + 371*pi/2) ** 2 = 1 - cos(-y + 371*pi/2) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : -cos(x + 355 * pi / 2) ** 2 * sin(y) ** 2 - cos(x + 355 * pi / 2) ** 2 * sin(-y + 371 * pi / 2) ** 2 + cos(x + 355 * pi / 2) ** 2 + sin(y) ** 2 = -sin(y)**2*cos(x + 355*pi/2)**2 + sin(y)**2 - sin(-y + 371*pi/2)**2*cos(x + 355*pi/2)**2 + cos(x + 355*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = cos(x + 355*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x) ** 2 * sin(y) ** 2 - sin(x) ** 2 * (-sin(-y + 371 * pi / 2)) ** 2 + sin(x) ** 2 + sin(y) ** 2 = -sin(x)**2*sin(y)**2 - sin(x)**2*sin(-y + 371*pi/2)**2 + sin(x)**2 + sin(y)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(y) = -sin(-y + 371*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (y) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x)**2*sin(y)**2 - sin(x)**2*cos(y)**2 = -sin(x)**2*(sin(y)**2 + cos(y)**2),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
end


lemma Trigo_0_11_UPWT_extend : -sin(23*pi/180)*cos(-8693*pi/180) - sin(-pi/6)/2 + sin(19*pi/45)/2=1/2:=
begin
have : sin(23 * pi / 180) * -cos((-8693) * pi / 180) - sin(-pi / 6) / 2 + sin(19 * pi / 45) / 2 = -sin(23*pi/180)*cos(-8693*pi/180) - sin(-pi/6)/2 + sin(19*pi/45)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(29843*pi/180) = -cos(-8693*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (29843*pi/180) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(23 * pi / 180) * -sin(29843 * pi / 180) - sin(-pi / 6) / 2 + sin(19 * pi / 45) / 2 = sin(23*pi/180)*sin(29843*pi/180) - sin(-pi/6)/2 + sin(19*pi/45)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(53*pi/180) = -sin(29843*pi/180),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (53*pi/180) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(23 * pi / 180) * cos(53 * pi / 180) + (-sin(-pi / 6) / 2 + sin(19 * pi / 45) / 2) = -sin(23*pi/180)*cos(53*pi/180) - sin(-pi/6)/2 + sin(19*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(53*pi/180) * cos(23*pi/180) = -sin(-pi/6) / 2 + sin(19*pi/45) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((23*pi/180) + (53*pi/180)) = sin(19*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin((23*pi/180) - (53*pi/180)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(53*pi/180) * cos(23*pi/180)) = sin(53*pi/180)*cos(23*pi/180),
{
ring,
},
have : -sin(23*pi/180)*cos(53*pi/180) + sin(53*pi/180)*cos(23*pi/180) = sin(pi/6),
{
have : sin(pi/6) = sin((53*pi/180) - (23*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_0_12_KMNE_extend : -sin(1405*pi/12)*cos(239*pi/12)/2=1/8:=
begin
have : cos(pi/12) = cos(239*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/12) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1213*pi/12) = sin(1405*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (1213*pi/12) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(1213*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/12) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*cos(pi/12)/2 = sin(pi/6)/4,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_13_AURP_extend : -4*sin(pi/12)*sin(1061*pi/12)*cos(pi/2) + 2*sin(pi/2)*cos(pi/6)=sqrt(3):=
begin
have : (-4) * sin(pi / 12) * sin(1061 * pi / 12) * cos(pi / 2) + 2 * sin(pi / 2) * cos(pi / 6) = -4*sin(pi/12)*sin(1061*pi/12)*cos(pi/2) + 2*sin(pi/2)*cos(pi/6),
{
field_simp at *,
},
have : cos(pi/12) = sin(1061*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * (2 * sin(pi / 12) * cos(pi / 12)) * cos(pi / 2) + 2 * sin(pi / 2) * cos(pi / 6) = -4*sin(pi/12)*cos(pi/12)*cos(pi/2) + 2*sin(pi/2)*cos(pi/6),
{
field_simp at *,
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
have : 2 * (sin(pi / 2) * cos(pi / 6) - sin(pi / 6) * cos(pi / 2)) = -2*sin(pi/6)*cos(pi/2) + 2*sin(pi/2)*cos(pi/6),
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
rw sin_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_0_14_HQRK_extend (h0 : sin(19403*pi/180)≠ 0) (h1 : (2*sin(19403*pi/180))≠ 0) (h2 : sin(19403*pi/180)≠ 0) : sin(23*pi/360)*sin(19403*pi/90)*cos(23*pi/360)/sin(19403*pi/180) + sin(37*pi/180)*cos(23*pi/180)=sqrt(3)/2:=
begin
have : 2 * sin(23 * pi / 360) * cos(23 * pi / 360) * sin(19403 * pi / 90) / (2 * sin(19403 * pi / 180)) + sin(37 * pi / 180) * cos(23 * pi / 180) = sin(23*pi/360)*sin(19403*pi/90)*cos(23*pi/360)/sin(19403*pi/180) + sin(37*pi/180)*cos(23*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/180) = 2 * sin(23*pi/360) * cos(23*pi/360),
{
have : sin(23*pi/180) = sin(2*(23*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(23 * pi / 180) * (sin(19403 * pi / 90) / (2 * sin(19403 * pi / 180))) + sin(37 * pi / 180) * cos(23 * pi / 180) = sin(23*pi/180)*sin(19403*pi/90)/(2*sin(19403*pi/180)) + sin(37*pi/180)*cos(23*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(19403*pi/180) = sin(19403*pi/90) / ( 2 * sin(19403*pi/180) ),
{
have : sin(19403*pi/90) = sin(2*(19403*pi/180)),
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
have : cos(37*pi/180) = cos(19403*pi/180),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (37*pi/180) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/180)*cos(37*pi/180) + sin(37*pi/180)*cos(23*pi/180) = sin(pi/3),
{
have : sin(pi/3) = sin((23*pi/180) + (37*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_0_15_ETRV_extend : tan(11*pi/3) + (sin(-pi)*sin(pi) + cos(-pi)*cos(pi))*sin(-3*pi/4) + sin(-2*pi)*sin(225*pi/4)=-sqrt(2)/2-sqrt(3):=
begin
have : tan(11 * pi / 3) + sin((-3) * pi / 4) * (sin(-pi) * sin(pi) + cos(-pi) * cos(pi)) + sin((-2) * pi) * sin(225 * pi / 4) = tan(11*pi/3) + (sin(-pi)*sin(pi) + cos(-pi)*cos(pi))*sin(-3*pi/4) + sin(-2*pi)*sin(225*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = sin(-pi) * sin(pi) + cos(-pi) * cos(pi),
{
have : cos(-2*pi) = cos((-pi) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11 * pi / 3) + sin((-3) * pi / 4) * cos((-2) * pi) - sin((-2) * pi) * -sin(225 * pi / 4) = tan(11*pi/3) + sin(-3*pi/4)*cos(-2*pi) + sin(-2*pi)*sin(225*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-3*pi/4) = -sin(225*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-3*pi/4) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-3) * pi / 4) * cos((-2) * pi) - sin((-2) * pi) * cos((-3) * pi / 4) + tan(11 * pi / 3) = tan(11*pi/3) + sin(-3*pi/4)*cos(-2*pi) - sin(-2*pi)*cos(-3*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/4) = sin(-3*pi/4) * cos(-2*pi) - sin(-2*pi) * cos(-3*pi/4),
{
have : sin(5*pi/4) = sin((-3*pi/4) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/3) = tan(-pi/3),
{
rw tan_eq_tan_add_int_mul_pi (11*pi/3) (-4),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/4) = -sin(pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_three,
rw sin_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_0_16_ZMIB_extend (h0 : cos(pi/12)≠ 0) (h1 : (2*cos(pi/12))≠ 0) : (sin(229*pi/4)/2 - sin(673*pi/12)/2)/(2*cos(pi/12)) + sin(5*pi/12)*sin(11*pi/12)=0:=
begin
have : (-sin(673 * pi / 12) / 2 + sin(229 * pi / 4) / 2) / (2 * cos(pi / 12)) + sin(5 * pi / 12) * sin(11 * pi / 12) = (sin(229*pi/4)/2 - sin(673*pi/12)/2)/(2*cos(pi/12)) + sin(5*pi/12)*sin(11*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) * cos(170*pi/3) = -sin(673*pi/12) / 2 + sin(229*pi/4) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((170*pi/3) + (7*pi/12)) = sin(229*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((170*pi/3) - (7*pi/12)) = sin(673*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(7*pi/12) * cos(170*pi/3))/(2*cos(pi/12)) = sin(7*pi/12)*cos(170*pi/3)/(2*cos(pi/12)),
{
ring,
},
have : - -cos(170 * pi / 3) * sin(7 * pi / 12) / (2 * cos(pi / 12)) + sin(5 * pi / 12) * sin(11 * pi / 12) = sin(7*pi/12)*cos(170*pi/3)/(2*cos(pi/12)) + sin(5*pi/12)*sin(11*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(170*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(pi / 6) / (2 * cos(pi / 12))) * sin(7 * pi / 12) + sin(5 * pi / 12) * sin(11 * pi / 12) = -sin(pi/6)*sin(7*pi/12)/(2*cos(pi/12)) + sin(5*pi/12)*sin(11*pi/12),
{
field_simp at *,
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
have : sin(7*pi/12) = cos(pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/12) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(11*pi/12) = sin(pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
ring_exp,
end


lemma Trigo_0_17_FTGL_extend : -sin(967*pi/6)=1/2:=
begin
have : cos(-113*pi/3) = -sin(967*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-113*pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos((-113) * pi / 3) = cos(-113*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1003*pi/6) = -cos(-113*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1003*pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-19*pi/6) = -sin(1003*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-19*pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-19*pi/6) = sin(-7*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-19*pi/6) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-7*pi/6) = -sin(7*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-7*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_18_TPOC_extend : -2*sin(221*pi/12)*cos(691*pi/12)=-1/2:=
begin
have : 2 * sin(221 * pi / 12) * -cos(691 * pi / 12) = -2*sin(221*pi/12)*cos(691*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/12) = -cos(691*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (7*pi/12) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) = sin(221*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/12) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/6) = 2 * sin(7*pi/12) * cos(7*pi/12),
{
have : sin(7*pi/6) = sin(2*(7*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_19_TYCU_extend (h0 : cos(11*pi/60)≠ 0) (h1 : (2*cos(11*pi/60))≠ 0) (h2 : (2*cos(4331*pi/60))≠ 0) : sin(3*pi/20)*cos(4331*pi/60) + (-sin(3*pi/40)**2 + cos(3*pi/40)**2)*sin(11*pi/30)/(2*cos(4331*pi/60))=sqrt(3)/2:=
begin
have : cos(11*pi/60) = cos(4331*pi/60),
{
rw cos_eq_cos_add_int_mul_two_pi (11*pi/60) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3 * pi / 20) * cos(11 * pi / 60) + sin(11 * pi / 30) * (-sin(3 * pi / 40) ** 2 + cos(3 * pi / 40) ** 2) / (2 * cos(11 * pi / 60)) = sin(3*pi/20)*cos(11*pi/60) + (-sin(3*pi/40)**2 + cos(3*pi/40)**2)*sin(11*pi/30)/(2*cos(11*pi/60)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/20) = -sin(3*pi/40) ** 2 + cos(3*pi/40) ** 2,
{
have : cos(3*pi/20) = cos(2*(3*pi/40)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3 * pi / 20) * cos(11 * pi / 60) + sin(11 * pi / 30) / (2 * cos(11 * pi / 60)) * cos(3 * pi / 20) = sin(3*pi/20)*cos(11*pi/60) + sin(11*pi/30)*cos(3*pi/20)/(2*cos(11*pi/60)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/60) = sin(11*pi/30) / ( 2 * cos(11*pi/60) ),
{
have : sin(11*pi/30) = sin(2*(11*pi/60)),
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
have : sin(3*pi/20)*cos(11*pi/60) + sin(11*pi/60)*cos(3*pi/20) = sin(pi/3),
{
have : sin(pi/3) = sin((3*pi/20) + (11*pi/60)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_0_20_BOHO_extend : (sin(pi/4)*sin(190*pi/3) + sin(pi/6)*cos(pi/4))*sin(5*pi/6) + sin(190*pi/3)*cos(1885*pi/12)=sqrt(2)/2:=
begin
have : -(-sin(pi / 6) * cos(pi / 4) + sin(pi / 4) * -sin(190 * pi / 3)) * sin(5 * pi / 6) - -sin(190 * pi / 3) * cos(1885 * pi / 12) = (sin(pi/4)*sin(190*pi/3) + sin(pi/6)*cos(pi/4))*sin(5*pi/6) + sin(190*pi/3)*cos(1885*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(190*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(pi / 4) * cos(pi / 6) - sin(pi / 6) * cos(pi / 4)) * sin(5 * pi / 6) - cos(pi / 6) * cos(1885 * pi / 12) = -(-sin(pi/6)*cos(pi/4) + sin(pi/4)*cos(pi/6))*sin(5*pi/6) - cos(pi/6)*cos(1885*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(pi/4) * cos(pi/6) - sin(pi/6) * cos(pi/4),
{
have : sin(pi/12) = sin((pi/4) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) * sin(5 * pi / 6) + -cos(1885 * pi / 12) * cos(pi / 6) = -sin(pi/12)*sin(5*pi/6) - cos(pi/6)*cos(1885*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = -cos(1885*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/12) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(pi/12)*sin(pi/6) + cos(pi/12)*cos(pi/6) = cos(pi/4),
{
have : cos(pi/4) = cos((pi/6) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_0_21_DDDQ_extend (h0 : sin(9*pi/4)≠ 0) (h1 : (2*sin(9*pi/4))≠ 0) : -tan(191*pi/6) + sin(193*pi/2)/(2*sin(9*pi/4))=(3*sqrt(2)+2*sqrt(3))/6:=
begin
have : sin(9*pi/2) = sin(193*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (9*pi/2) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(9*pi/4) = sin(9*pi/2) / ( 2 * sin(9*pi/4) ),
{
have : sin(9*pi/2) = sin(2*(9*pi/4)),
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
have : cos(9 * pi / 4) + -tan(191 * pi / 6) = -tan(191*pi/6) + cos(9*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-11*pi/6) = -tan(191*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-11*pi/6) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-11*pi/6) = tan(pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-11*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_six,
have : cos(9*pi/4) = cos(pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (9*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_0_22_WAJU_extend (h0 : (cos(-pi/3)+2*cos(4*pi/3)**2+2)≠ 0) (h1 : (2*cos(4*pi/3)**2+cos(-pi/3)+2)≠ 0) (h2 : sin(4*pi/3)≠ 0) (h3 : (2*sin(4*pi/3))≠ 0) (h4 : (2*(sin(8*pi/3)/(2*sin(4*pi/3)))**2+cos(-pi/3)+2)≠ 0) (h5 : (sin(8*pi/3)**2/(2*sin(4*pi/3)**2)+cos(-pi/3)+2)≠ 0) (h6 : (2*sin(4*pi/3)**2)≠ 0) (h7 : (-3*cos(-pi/9)+sin(8*pi/3)**2/(2*sin(4*pi/3)**2)+2+4*cos(-pi/9)**3)≠ 0) (h8 : (sin(8*pi/3)**2/(2*sin(4*pi/3)**2)+(4*cos(-pi/9)**3-3*cos(-pi/9))+2)≠ 0) : (-3 - 2*sin(1135*pi/6)**3 + sin(5*pi/6) + sin(5*pi/3)**2)/(-3*cos(-pi/9) + sin(8*pi/3)**2/(2*sin(4*pi/3)**2) + 2 + 4*cos(-pi/9)**3)=-1/2:=
begin
have : (-3 - 2 * sin(1135 * pi / 6) ** 3 + sin(5 * pi / 6) + sin(5 * pi / 3) ** 2) / (sin(8 * pi / 3) ** 2 / (2 * sin(4 * pi / 3) ** 2) + (4 * cos(-pi / 9) ** 3 - 3 * cos(-pi / 9)) + 2) = (-3 - 2*sin(1135*pi/6)**3 + sin(5*pi/6) + sin(5*pi/3)**2)/(-3*cos(-pi/9) + sin(8*pi/3)**2/(2*sin(4*pi/3)**2) + 2 + 4*cos(-pi/9)**3),
{
field_simp at *,
repeat {left},
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
have : (-3 - 2 * sin(1135 * pi / 6) ** 3 + sin(5 * pi / 6) + sin(5 * pi / 3) ** 2) / (2 * (sin(8 * pi / 3) / (2 * sin(4 * pi / 3))) ** 2 + cos(-pi / 3) + 2) = (-3 - 2*sin(1135*pi/6)**3 + sin(5*pi/6) + sin(5*pi/3)**2)/(sin(8*pi/3)**2/(2*sin(4*pi/3)**2) + cos(-pi/3) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : (sin(5 * pi / 6) + sin(5 * pi / 3) ** 2 + 2 * (-sin(1135 * pi / 6)) ** 3 - 3) / (cos(-pi / 3) + 2 * cos(4 * pi / 3) ** 2 + 2) = (-3 - 2*sin(1135*pi/6)**3 + sin(5*pi/6) + sin(5*pi/3)**2)/(2*cos(4*pi/3)**2 + cos(-pi/3) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(1135*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw cos_pi_div_three,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
have : sin(5*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
have : cos(-pi/3) = cos(pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
have : cos(4*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_0_23_YNNF_extend : -sqrt(3)/2 - sin(1181*pi/4)*cos(473*pi/4) + sqrt(3)*cos(473*pi/4)**2=1/2:=
begin
have : -sqrt 3 / 2 + -sin(1181 * pi / 4) * cos(473 * pi / 4) + sqrt 3 * cos(473 * pi / 4) ** 2 = -sqrt(3)/2 - sin(1181*pi/4)*cos(473*pi/4) + sqrt(3)*cos(473*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(497*pi/4) = -sin(1181*pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (497*pi/4) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 / 2 + sin(497 * pi / 4) * cos(473 * pi / 4) + sqrt 3 * cos(473 * pi / 4) ** 2 = -sqrt(3)/2 + sin(497*pi/4)*cos(473*pi/4) + sqrt(3)*cos(473*pi/4)**2,
{
field_simp at *,
},
have : sin(pi/4) = sin(497*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/4) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 4) * cos(473 * pi / 4) + sqrt 3 * cos(473 * pi / 4) ** 2 - sqrt 3 / 2 = -sqrt(3)/2 + sin(pi/4)*cos(473*pi/4) + sqrt(3)*cos(473*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = cos(473*pi/4),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/4) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_pi_div_four,
rw cos_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_24_FUOI_extend : ((-sin(25*pi/24)**2 + cos(25*pi/24)**2)*sin(122*pi) + sin(25*pi/12)*cos(-2*pi) + sin(5*pi/12))*(-sin(25*pi/12)*cos(-2*pi) - (-sin(25*pi/24)**2 + cos(25*pi/24)**2)*sin(122*pi) + sin(5*pi/12))=sqrt(3)/2:=
begin
have : (-sin(25 * pi / 12) * cos((-2) * pi) - sin(122 * pi) * (-sin(25 * pi / 24) ** 2 + cos(25 * pi / 24) ** 2) + sin(5 * pi / 12)) * (sin(122 * pi) * (-sin(25 * pi / 24) ** 2 + cos(25 * pi / 24) ** 2) + sin(25 * pi / 12) * cos((-2) * pi) + sin(5 * pi / 12)) = ((-sin(25*pi/24)**2 + cos(25*pi/24)**2)*sin(122*pi) + sin(25*pi/12)*cos(-2*pi) + sin(5*pi/12))*(-sin(25*pi/12)*cos(-2*pi) - (-sin(25*pi/24)**2 + cos(25*pi/24)**2)*sin(122*pi) + sin(5*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/12) = -sin(25*pi/24) ** 2 + cos(25*pi/24) ** 2,
{
have : cos(25*pi/12) = cos(2*(25*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(122 * pi) * cos(25 * pi / 12) + sin(25 * pi / 12) * cos((-2) * pi) + sin(5 * pi / 12)) * (-sin(25 * pi / 12) * cos((-2) * pi) - sin(122 * pi) * cos(25 * pi / 12) + sin(5 * pi / 12)) = (-sin(25*pi/12)*cos(-2*pi) - sin(122*pi)*cos(25*pi/12) + sin(5*pi/12))*(sin(122*pi)*cos(25*pi/12) + sin(25*pi/12)*cos(-2*pi) + sin(5*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi) = sin(122*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-2*pi) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-(sin(25 * pi / 12) * cos((-2) * pi) + sin((-2) * pi) * cos(25 * pi / 12)) + sin(5 * pi / 12)) * (sin(25 * pi / 12) * cos((-2) * pi) + sin((-2) * pi) * cos(25 * pi / 12) + sin(5 * pi / 12)) = (sin(-2*pi)*cos(25*pi/12) + sin(25*pi/12)*cos(-2*pi) + sin(5*pi/12))*(-sin(25*pi/12)*cos(-2*pi) - sin(-2*pi)*cos(25*pi/12) + sin(5*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(25*pi/12) * cos(-2*pi) + sin(-2*pi) * cos(25*pi/12),
{
have : sin(pi/12) = sin((25*pi/12) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi/12) + sin(5*pi/12))*(sin(pi/12) + sin(5*pi/12)) = -sin(pi/12)**2 + sin(5*pi/12)**2,
{
ring_exp,
},
rw this,
have : sin(5*pi/12)**2 = 1/2 - cos(5*pi/6)/2,
{
have : cos(5*pi/6) = cos(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
rw cos_pi_div_six,
have : cos(5*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_25_VFTE_extend : -6*sin(535*pi/18)*cos(-pi) - 6*sin(-pi)*cos(535*pi/18) + 8*(sin(-pi)*cos(535*pi/18) + sin(535*pi/18)*cos(-pi))**3=-1:=
begin
have : (-6) * (sin(535 * pi / 18) * cos(-pi) + sin(-pi) * cos(535 * pi / 18)) + 8 * (sin(535 * pi / 18) * cos(-pi) + sin(-pi) * cos(535 * pi / 18)) ** 3 = -6*sin(535*pi/18)*cos(-pi) - 6*sin(-pi)*cos(535*pi/18) + 8*(sin(-pi)*cos(535*pi/18) + sin(535*pi/18)*cos(-pi))**3,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(517*pi/18) = sin(535*pi/18) * cos(-pi) + sin(-pi) * cos(535*pi/18),
{
have : sin(517*pi/18) = sin((535*pi/18) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * ((-4) * sin(517 * pi / 18) ** 3 + 3 * sin(517 * pi / 18)) = -6*sin(517*pi/18) + 8*sin(517*pi/18)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(517*pi/6) = -4 * sin(517*pi/18) ** 3 + 3 * sin(517*pi/18),
{
have : sin(517*pi/6) = sin(3*(517*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * -sin(517 * pi / 6) = -2*sin(517*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(517*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_26_KHEN_extend : cos(-513*pi/2)/2 + sin(3083*pi/12)**2 - cos(772*pi/3)/2 + sin(5*pi/12)**2=5/4:=
begin
have : sin(3083 * pi / 12) ** 2 + (cos((-513) * pi / 2) / 2 - cos(772 * pi / 3) / 2) + sin(5 * pi / 12) ** 2 = cos(-513*pi/2)/2 + sin(3083*pi/12)**2 - cos(772*pi/3)/2 + sin(5*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) * sin(3083*pi/12) = cos(-513*pi/2) / 2 - cos(772*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((5*pi/12) + (3083*pi/12)) = cos(772*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/12) - (3083*pi/12)) = cos(-513*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(5*pi/12) * sin(3083*pi/12)) = sin(5*pi/12)*sin(3083*pi/12),
{
ring,
},
have : sin(1331*pi/12) = sin(3083*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (1331*pi/12) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1331 * pi / 12) ** 2 + sin(1331 * pi / 12) * sin(5 * pi / 12) + sin(5 * pi / 12) ** 2 = sin(1331*pi/12)**2 + sin(5*pi/12)*sin(1331*pi/12) + sin(5*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(1331*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : sin(5*pi/12)**2 = 1/2 - cos(5*pi/6)/2,
{
have : cos(5*pi/6) = cos(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : sin(pi/12)*sin(5*pi/12) = -cos(pi/2)/2 + cos(pi/3)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((5*pi/12) + (pi/12)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/12) - (pi/12)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw cos_pi_div_six,
rw cos_pi_div_two,
rw cos_pi_div_three,
have : cos(5*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_27_YBZQ_extend : -sin(-x/2 + 128*pi)**2 - sqrt(3)*sin(x + 27*pi)/2 + 1/2=cos(x-pi/3):=
begin
have : -(-sin(-x / 2 + 128 * pi)) ** 2 - sqrt 3 * sin(x + 27 * pi) / 2 + 1 / 2 = -sin(-x/2 + 128*pi)**2 - sqrt(3)*sin(x + 27*pi)/2 + 1/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x/2) = -sin(-x/2 + 128*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (x/2) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * sin(x + 27 * pi) / 2 + (1 - 2 * sin(x / 2) ** 2) / 2 = -sin(x/2)**2 - sqrt(3)*sin(x + 27*pi)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = 1 - 2 * sin(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * -sin(x + 27 * pi) / 2 + cos(x) / 2 = -sqrt(3)*sin(x + 27*pi)/2 + cos(x)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -sin(x + 27*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi/3) = sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
{
have : cos(x-pi/3) = cos((x) - (pi/3)),
{
apply congr_arg,
ring,
},
rw cos_sub,
ring,
},
rw this,
rw sin_pi_div_three,
rw cos_pi_div_three,
field_simp,
end


lemma Trigo_0_28_MHBJ_extend : -sin(-5747*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180)=1/2:=
begin
have : -cos(43 * pi / 180) * sin((-5747) * pi / 180) + sin(43 * pi / 180) * cos(13 * pi / 180) = -sin(-5747*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13037*pi/180) = sin(-5747*pi/180),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (13037*pi/180) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(13037 * pi / 180) * cos(43 * pi / 180) + sin(43 * pi / 180) * cos(13 * pi / 180) = -cos(43*pi/180)*cos(13037*pi/180) + sin(43*pi/180)*cos(13*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17473*pi/180) = -cos(13037*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (17473*pi/180) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(17473 * pi / 180) * cos(43 * pi / 180) + sin(43 * pi / 180) * cos(13 * pi / 180) = sin(17473*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = -sin(17473*pi/180),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (13*pi/180) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180) = sin(pi/6),
{
have : sin(pi/6) = sin((43*pi/180) - (13*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_0_29_ATAD_extend (h0 : sin(13*pi/360)≠ 0) (h1 : (2*sin(13*pi/360))≠ 0) (h2 : (2*sin(13*pi/360)**2)≠ 0) : -sin(13*pi/180)*cos(73*pi/180) + (-1 + sin(13*pi/180)**2/(2*sin(13*pi/360)**2))*(sin(-2*pi)*cos(433*pi/180) + sin(433*pi/180)*cos(-2*pi))=sqrt(3)/2:=
begin
have : -sin(13 * pi / 180) * cos(73 * pi / 180) + (-1 + 2 * (sin(13 * pi / 180) / (2 * sin(13 * pi / 360))) ** 2) * (sin((-2) * pi) * cos(433 * pi / 180) + sin(433 * pi / 180) * cos((-2) * pi)) = -sin(13*pi/180)*cos(73*pi/180) + (-1 + sin(13*pi/180)**2/(2*sin(13*pi/360)**2))*(sin(-2*pi)*cos(433*pi/180) + sin(433*pi/180)*cos(-2*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/360) = sin(13*pi/180) / ( 2 * sin(13*pi/360) ),
{
have : sin(13*pi/180) = sin(2*(13*pi/360)),
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
have : -sin(13 * pi / 180) * cos(73 * pi / 180) + (-1 + 2 * cos(13 * pi / 360) ** 2) * (sin(433 * pi / 180) * cos((-2) * pi) + sin((-2) * pi) * cos(433 * pi / 180)) = -sin(13*pi/180)*cos(73*pi/180) + (-1 + 2*cos(13*pi/360)**2)*(sin(-2*pi)*cos(433*pi/180) + sin(433*pi/180)*cos(-2*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(73*pi/180) = sin(433*pi/180) * cos(-2*pi) + sin(-2*pi) * cos(433*pi/180),
{
have : sin(73*pi/180) = sin((433*pi/180) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(13 * pi / 180) * cos(73 * pi / 180) + sin(73 * pi / 180) * (2 * cos(13 * pi / 360) ** 2 - 1) = -sin(13*pi/180)*cos(73*pi/180) + (-1 + 2*cos(13*pi/360)**2)*sin(73*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/180) = 2 * cos(13*pi/360) ** 2 - 1,
{
have : cos(13*pi/180) = cos(2*(13*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -sin(13*pi/180)*cos(73*pi/180) + sin(73*pi/180)*cos(13*pi/180) = sin(pi/3),
{
have : sin(pi/3) = sin((73*pi/180) - (13*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_0_30_JBJQ_extend (h0 : cos(13*pi/12)≠ 0) (h1 : (2*cos(13*pi/12))≠ 0) : -sin(pi/3)*sin(13*pi/6)/(2*cos(13*pi/12)) + 2*sin(pi/8)**2 - cos(13*pi/12)*cos(161*pi/3)=1:=
begin
have : -sin(pi / 3) * (sin(13 * pi / 6) / (2 * cos(13 * pi / 12))) + 2 * sin(pi / 8) ** 2 - cos(13 * pi / 12) * cos(161 * pi / 3) = -sin(pi/3)*sin(13*pi/6)/(2*cos(13*pi/12)) + 2*sin(pi/8)**2 - cos(13*pi/12)*cos(161*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/12) = sin(13*pi/6) / ( 2 * cos(13*pi/12) ),
{
have : sin(13*pi/6) = sin(2*(13*pi/12)),
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
have : -sin(pi / 3) * sin(13 * pi / 12) + 2 * sin(pi / 8) ** 2 - cos(161 * pi / 3) * cos(13 * pi / 12) = -sin(pi/3)*sin(13*pi/12) + 2*sin(pi/8)**2 - cos(13*pi/12)*cos(161*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(161*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 8) ** 2 - (sin(13 * pi / 12) * sin(pi / 3) + cos(13 * pi / 12) * cos(pi / 3)) = -sin(pi/3)*sin(13*pi/12) + 2*sin(pi/8)**2 - cos(pi/3)*cos(13*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/4) = sin(13*pi/12) * sin(pi/3) + cos(13*pi/12) * cos(pi/3),
{
have : cos(3*pi/4) = cos((13*pi/12) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8)**2 = 1/2 - cos(pi/4)/2,
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
have : cos(3*pi/4) = -cos(pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_31_HOMZ_extend : -sqrt(3)*cos(2081*pi/12) - cos(3227*pi/12)=sqrt(2):=
begin
have : sqrt 3 * -cos(2081 * pi / 12) - cos(3227 * pi / 12) = -sqrt(3)*cos(2081*pi/12) - cos(3227*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(2081*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(pi / 12) - cos(3227 * pi / 12) = sqrt(3)*sin(pi/12) - cos(3227*pi/12),
{
field_simp at *,
},
have : sin(1001*pi/12) = cos(3227*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1001*pi/12) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(pi / 12) + -sin(1001 * pi / 12) = sqrt(3)*sin(pi/12) - sin(1001*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(1001*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3)*sin(pi/12) = 2*sin(pi/12)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/12) = 2*sin(pi/6)*cos(pi/12),
{
field_simp,
},
rw this,
have : 2*sin(pi/12)*cos(pi/6) + 2*sin(pi/6)*cos(pi/12) = 2*sin(pi/4),
{
have : sin(pi/4) = sin(pi/12)*cos(pi/6) + sin(pi/6)*cos(pi/12),
{
have : sin(pi/4) = sin((pi/6) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
rw sin_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_0_32_IVFV_extend : -sin(4591*pi/30)/2 + sin(pi/15)*sin(2*pi/5) + sin(241*pi/6)/2=1/2:=
begin
have : cos(pi/3) = sin(241*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/15) = -sin(4591*pi/30),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/15) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 15) * sin(2 * pi / 5) + (cos(pi / 3) / 2 + cos(7 * pi / 15) / 2) = cos(7*pi/15)/2 + sin(pi/15)*sin(2*pi/5) + cos(pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/5) * cos(pi/15) = cos(pi/3) / 2 + cos(7*pi/15) / 2,
{
rw cos_mul_cos,
have : cos((2*pi/5) + (pi/15)) = cos(7*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi/5) - (pi/15)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(2*pi/5) * cos(pi/15)) = cos(pi/15)*cos(2*pi/5),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(pi/15)*sin(2*pi/5) + cos(pi/15)*cos(2*pi/5) = cos(pi/3),
{
have : cos(pi/3) = cos((2*pi/5) - (pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw this,
rw cos_pi_div_three,
end


lemma Trigo_0_33_HFRQ_extend : -16*(-sin(2*pi)*cos(33*pi/16) + sin(33*pi/16)*cos(2*pi))**4*cos(pi/16)**4 + sin(411*pi/8)**4=sqrt(2)/2:=
begin
have : (-16) * (sin(33 * pi / 16) * cos(2 * pi) - sin(2 * pi) * cos(33 * pi / 16)) ** 4 * cos(pi / 16) ** 4 + sin(411 * pi / 8) ** 4 = -16*(-sin(2*pi)*cos(33*pi/16) + sin(33*pi/16)*cos(2*pi))**4*cos(pi/16)**4 + sin(411*pi/8)**4,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/16) = sin(33*pi/16) * cos(2*pi) - sin(2*pi) * cos(33*pi/16),
{
have : sin(pi/16) = sin((33*pi/16) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-16) * sin(pi / 16) ** 4 * cos(pi / 16) ** 4 + (-sin(411 * pi / 8)) ** 4 = -16*sin(pi/16)**4*cos(pi/16)**4 + sin(411*pi/8)**4,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = -sin(411*pi/8),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(2 * sin(pi / 16) * cos(pi / 16)) ** 4 + cos(pi / 8) ** 4 = -16*sin(pi/16)**4*cos(pi/16)**4 + cos(pi/8)**4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : -sin(pi/8)**4 + cos(pi/8)**4 = (-sin(pi/8)**2 + cos(pi/8)**2)*(sin(pi/8)**2 + cos(pi/8)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : -sin(pi/8)**2 + cos(pi/8)**2 = cos(pi/4),
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
rw cos_pi_div_four,
norm_num,
end


lemma Trigo_0_34_TZIF_extend (h0 : cos(pi/8)≠ 0) (h1 : (1-tan(pi/8)**2)≠ 0) : -2*sin(-1295*pi/24)*sin(1303*pi/24) + 2*tan(pi/8)/(1 - tan(pi/8)**2)=(3-sqrt(2))/2:=
begin
have : (-2) * sin((-1295) * pi / 24) * sin(1303 * pi / 24) + 2 * tan(pi / 8) / (1 - tan(pi / 8) ** 2) = -2*sin(-1295*pi/24)*sin(1303*pi/24) + 2*tan(pi/8)/(1 - tan(pi/8)**2),
{
field_simp at *,
},
have : cos(pi/3) - cos(433*pi/4) = -2 * sin(-1295*pi/24) * sin(1303*pi/24),
{
rw cos_sub_cos,
have : sin(((pi/3) + (433*pi/4))/2) = sin(1303*pi/24),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (433*pi/4))/2) = sin(-1295*pi/24),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(pi/3) - cos(433*pi/4)) + 2*tan(pi/8)/(1 - tan(pi/8)**2) = -cos(433*pi/4)+cos(pi/3)+2*tan(pi/8)/(1-tan(pi/8)**2),
{
ring,
},
conv {to_lhs, rw this,},
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
have : sin(-pi/4) = -cos(433*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-pi/4) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/4) = -sin(pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_four,
rw cos_pi_div_three,
rw tan_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_0_35_DDKB_extend : -sin(727*pi/9)*cos(389*pi/18) + cos(2*pi/9)*cos(595*pi/9)=1/2:=
begin
have : -cos(389 * pi / 18) * sin(727 * pi / 9) + cos(2 * pi / 9) * cos(595 * pi / 9) = -sin(727*pi/9)*cos(389*pi/18) + cos(2*pi/9)*cos(595*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = cos(389*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 9) * sin(727 * pi / 9) + cos(595 * pi / 9) * cos(2 * pi / 9) = -sin(pi/9)*sin(727*pi/9) + cos(2*pi/9)*cos(595*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = cos(595*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/9) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = sin(727*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/9) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/9)*sin(2*pi/9) + cos(pi/9)*cos(2*pi/9) = cos(pi/3),
{
have : cos(pi/3) = cos((pi/9) + (2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_three,
end


lemma Trigo_0_36_ITDD_extend : -(cos(-3*pi/2)*cos(-pi/3) - sin(-3*pi/2)*sin(-pi/3))*sin(2*pi) - sin(871*pi/6)*cos(2*pi)=1/2:=
begin
have : -sin(2 * pi) * (-sin((-3) * pi / 2) * sin(-pi / 3) + cos((-3) * pi / 2) * cos(-pi / 3)) - sin(871 * pi / 6) * cos(2 * pi) = -(cos(-3*pi/2)*cos(-pi/3) - sin(-3*pi/2)*sin(-pi/3))*sin(2*pi) - sin(871*pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-11*pi/6) = -sin(-3*pi/2) * sin(-pi/3) + cos(-3*pi/2) * cos(-pi/3),
{
have : cos(-11*pi/6) = cos((-3*pi/2) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(2 * pi) * cos((-11) * pi / 6) + -sin(871 * pi / 6) * cos(2 * pi) = -sin(2*pi)*cos(-11*pi/6) - sin(871*pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-11*pi/6) = -sin(871*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-11*pi/6) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-11) * pi / 6) * cos(2 * pi) - sin(2 * pi) * cos((-11) * pi / 6) = -sin(2*pi)*cos(-11*pi/6) + sin(-11*pi/6)*cos(2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-23*pi/6) = sin(-11*pi/6) * cos(2*pi) - sin(2*pi) * cos(-11*pi/6),
{
have : sin(-23*pi/6) = sin((-11*pi/6) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-23*pi/6) = -sin(23*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-23*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(23*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (23*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_37_QISN_extend : -1/2 + 2*sin(2117*pi/12)*cos(265*pi/4)=sqrt(3)/2:=
begin
have : (-1) / 2 - 2 * sin(2117 * pi / 12) * -cos(265 * pi / 4) = -1/2 + 2*sin(2117*pi/12)*cos(265*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(323*pi/4) = -cos(265*pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (323*pi/4) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / 2 + 2 * -cos(323 * pi / 4) * sin(2117 * pi / 12) = -1/2 - 2*sin(2117*pi/12)*cos(323*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(323*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 4) * sin(2117 * pi / 12) - 1 / 2 = -1/2 + 2*sin(pi/4)*sin(2117*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(2117*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*sin(pi/4)*cos(pi/12) = sin(pi/3) + sin(pi/6),
{
have : sin(pi/4)*cos(pi/12) = sin(pi/6)/2 + sin(pi/3)/2,
{
rw sin_mul_cos,
have : sin((pi/4) + (pi/12)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/4) - (pi/12)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
rw sin_pi_div_three,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_38_UBYU_extend : 3/4 - 3*(9*sin(131*pi/108) - 12*sin(131*pi/108)**3 - 4*(3*sin(131*pi/108) - 4*sin(131*pi/108)**3)**3)**2/2=3*sqrt(3)/8:=
begin
have : 3 / 4 - 3 * (3 * ((-4) * sin(131 * pi / 108) ** 3 + 3 * sin(131 * pi / 108)) - 4 * ((-4) * sin(131 * pi / 108) ** 3 + 3 * sin(131 * pi / 108)) ** 3) ** 2 / 2 = 3/4 - 3*(9*sin(131*pi/108) - 12*sin(131*pi/108)**3 - 4*(3*sin(131*pi/108) - 4*sin(131*pi/108)**3)**3)**2/2,
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(131*pi/36) = -4 * sin(131*pi/108) ** 3 + 3 * sin(131*pi/108),
{
have : sin(131*pi/36) = sin(3*(131*pi/108)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 3 / 4 - 3 * ((-4) * sin(131 * pi / 36) ** 3 + 3 * sin(131 * pi / 36)) ** 2 / 2 = 3/4 - 3*(3*sin(131*pi/36) - 4*sin(131*pi/36)**3)**2/2,
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(131*pi/12) = -4 * sin(131*pi/36) ** 3 + 3 * sin(131*pi/36),
{
have : sin(131*pi/12) = sin(3*(131*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(131*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
rw cos_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_0_39_OVOT_extend : -sin(pi/10)*cos(2147*pi/30) + (1 - 2*sin(pi/20)**2)*sin(4633*pi/30)=sqrt(3)/2:=
begin
have : sin(13*pi/30) = sin(4633*pi/30),
{
rw sin_eq_sin_add_int_mul_two_pi (13*pi/30) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 10) * cos(2147 * pi / 30) + sin(13 * pi / 30) * (1 - 2 * sin(pi / 20) ** 2) = -sin(pi/10)*cos(2147*pi/30) + (1 - 2*sin(pi/20)**2)*sin(13*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/10) = 1 - 2 * sin(pi/20) ** 2,
{
have : cos(pi/10) = cos(2*(pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/30) = cos(2147*pi/30),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (13*pi/30) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/10)*cos(13*pi/30) + sin(13*pi/30)*cos(pi/10) = sin(pi/3),
{
have : sin(pi/3) = sin((13*pi/30) - (pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_0_40_UUSW_extend : 2*cos(pi/6)*cos(995*pi/12) + 2*(-4*sin(pi/18)**3 + 3*sin(pi/18))*sin(995*pi/12) + 1=1-sqrt(2):=
begin
have : 2 * cos(pi / 6) * cos(995 * pi / 12) + 2 * ((-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18)) * sin(995 * pi / 12) + 1 = 2*cos(pi/6)*cos(995*pi/12) + 2*(-4*sin(pi/18)**3 + 3*sin(pi/18))*sin(995*pi/12) + 1,
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
have : 2 * (sin(995 * pi / 12) * sin(pi / 6) + cos(995 * pi / 12) * cos(pi / 6)) + 1 = 2*cos(pi/6)*cos(995*pi/12) + 2*sin(pi/6)*sin(995*pi/12) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(331*pi/4) = sin(995*pi/12) * sin(pi/6) + cos(995*pi/12) * cos(pi/6),
{
have : cos(331*pi/4) = cos((995*pi/12) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * -cos(331 * pi / 4) = 2*cos(331*pi/4) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = -cos(331*pi/4),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/4) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_41_MKYG_extend (h0 : sin(pi/2)≠ 0) (h1 : (4*sin(pi/2))≠ 0) (h2 : (2*sin(pi/2))≠ 0) : -sin(11*pi)/(4*sin(pi/2)) + cos(pi/3)/2=1/4:=
begin
have : sin(pi) = sin(11*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (pi) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(pi) / (2 * sin(pi / 2))) / 2 + cos(pi / 3) / 2 = -sin(pi)/(4*sin(pi/2)) + cos(pi/3)/2,
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
have : cos(pi / 3) / 2 - cos(pi / 2) / 2 = -cos(pi/2)/2 + cos(pi/3)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) * sin(pi/12) = cos(pi/3) / 2 - cos(pi/2) / 2,
{
rw sin_mul_sin,
have : cos((5*pi/12) + (pi/12)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/12) - (pi/12)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(5*pi/12) * sin(pi/12)) = sin(pi/12)*sin(5*pi/12),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_42_BTLV_extend : 2*sin(13*pi/360)*cos(13*pi/360)*cos(8*pi/45) - cos(33853*pi/180)*cos(17939*pi/90)=sqrt(2)/2:=
begin
have : cos(13*pi/180) = cos(33853*pi/180),
{
rw cos_eq_cos_add_int_mul_two_pi (13*pi/180) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = 2 * sin(13*pi/360) * cos(13*pi/360),
{
have : sin(13*pi/180) = sin(2*(13*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 180) * cos(8 * pi / 45) + -cos(17939 * pi / 90) * cos(13 * pi / 180) = sin(13*pi/180)*cos(8*pi/45) - cos(13*pi/180)*cos(17939*pi/90),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8*pi/45) = -cos(17939*pi/90),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/45) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180)*cos(8*pi/45) = -sin(19*pi/180)/2 + sin(pi/4)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((8*pi/45) + (13*pi/180)) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((8*pi/45) - (13*pi/180)) = sin(19*pi/180),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(8*pi/45)*cos(13*pi/180) = sin(19*pi/180)/2 + sin(pi/4)/2,
{
rw sin_mul_cos,
have : sin((8*pi/45) + (13*pi/180)) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((8*pi/45) - (13*pi/180)) = sin(19*pi/180),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_0_43_EYFQ_extend : (-1 + 2*(sin(-pi)*sin(-343*pi/360) + cos(-pi)*cos(-343*pi/360))**2)*sin(13*pi/180) - sin(17*pi/180)*sin(27977*pi/180)=1/2:=
begin
have : (-1 + 2 * (sin((-343) * pi / 360) * sin(-pi) + cos((-343) * pi / 360) * cos(-pi)) ** 2) * sin(13 * pi / 180) - sin(17 * pi / 180) * sin(27977 * pi / 180) = (-1 + 2*(sin(-pi)*sin(-343*pi/360) + cos(-pi)*cos(-343*pi/360))**2)*sin(13*pi/180) - sin(17*pi/180)*sin(27977*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/360) = sin(-343*pi/360) * sin(-pi) + cos(-343*pi/360) * cos(-pi),
{
have : cos(17*pi/360) = cos((-343*pi/360) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1 + 2 * cos(17 * pi / 360) ** 2) * sin(13 * pi / 180) + sin(17 * pi / 180) * -sin(27977 * pi / 180) = (-1 + 2*cos(17*pi/360)**2)*sin(13*pi/180) - sin(17*pi/180)*sin(27977*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/180) = -sin(27977*pi/180),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/180) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 180) * (2 * cos(17 * pi / 360) ** 2 - 1) + sin(17 * pi / 180) * cos(13 * pi / 180) = (-1 + 2*cos(17*pi/360)**2)*sin(13*pi/180) + sin(17*pi/180)*cos(13*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/180) = 2 * cos(17*pi/360) ** 2 - 1,
{
have : cos(17*pi/180) = cos(2*(17*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180)*cos(17*pi/180) = -sin(pi/45)/2 + sin(pi/6)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((17*pi/180) + (13*pi/180)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((17*pi/180) - (13*pi/180)) = sin(pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(17*pi/180)*cos(13*pi/180) = sin(pi/45)/2 + sin(pi/6)/2,
{
rw sin_mul_cos,
have : sin((17*pi/180) + (13*pi/180)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((17*pi/180) - (13*pi/180)) = sin(pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_44_GTGQ_extend : -sin(7*pi/90)*sin(1027*pi/90) + (sin(-pi/6)*sin(2351*pi/45) + sin(23*pi/90)*cos(-pi/6))*cos(7*pi/90)=1/2:=
begin
have : cos(23*pi/90) = sin(2351*pi/45),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (23*pi/90) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(7 * pi / 90) * sin(1027 * pi / 90) + (sin(23 * pi / 90) * cos(-pi / 6) + sin(-pi / 6) * cos(23 * pi / 90)) * cos(7 * pi / 90) = -sin(7*pi/90)*sin(1027*pi/90) + (sin(-pi/6)*cos(23*pi/90) + sin(23*pi/90)*cos(-pi/6))*cos(7*pi/90),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/45) = sin(23*pi/90) * cos(-pi/6) + sin(-pi/6) * cos(23*pi/90),
{
have : sin(4*pi/45) = sin((23*pi/90) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 90) * -sin(1027 * pi / 90) + sin(4 * pi / 45) * cos(7 * pi / 90) = -sin(7*pi/90)*sin(1027*pi/90) + sin(4*pi/45)*cos(7*pi/90),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/45) = -sin(1027*pi/90),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/45) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/90)*cos(4*pi/45) + sin(4*pi/45)*cos(7*pi/90) = sin(pi/6),
{
have : sin(pi/6) = sin((4*pi/45) + (7*pi/90)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_0_45_DCSU_extend (h0 : cos(1819*pi/12)≠ 0) (h1 : (2*cos(1819*pi/12))≠ 0) : -cos(5*pi/12)*cos(1424*pi/3)/(2*cos(1819*pi/12))=1/4:=
begin
have : -cos(1424 * pi / 3) * cos(5 * pi / 12) / (2 * cos(1819 * pi / 12)) = -cos(5*pi/12)*cos(1424*pi/3)/(2*cos(1819*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1819*pi/6) = cos(1424*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1819*pi/6) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(1819 * pi / 6) / (2 * cos(1819 * pi / 12))) * cos(5 * pi / 12) = -sin(1819*pi/6)*cos(5*pi/12)/(2*cos(1819*pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1819*pi/12) = sin(1819*pi/6) / ( 2 * cos(1819*pi/12) ),
{
have : sin(1819*pi/6) = sin(2*(1819*pi/12)),
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
have : sin(5*pi/12) = -sin(1819*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/12) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12)*cos(5*pi/12) = sin(0)/2 + sin(5*pi/6)/2,
{
rw sin_mul_cos,
have : sin((5*pi/12) + (5*pi/12)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((5*pi/12) - (5*pi/12)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_five_pi_div_six,
norm_num,
end


lemma Trigo_0_46_CPES_extend : (((-1 + 2*cos(-pi/3)**2)*sin(pi/2) + sin(-2*pi/3)*cos(pi/2))*sin(5*pi/12) + cos(-pi/6)*cos(5*pi/12))*sin(7*pi/12)=-1/4:=
begin
have : ((sin(pi / 2) * (2 * cos(-pi / 3) ** 2 - 1) + sin((-2) * pi / 3) * cos(pi / 2)) * sin(5 * pi / 12) + cos(-pi / 6) * cos(5 * pi / 12)) * sin(7 * pi / 12) = (((-1 + 2*cos(-pi/3)**2)*sin(pi/2) + sin(-2*pi/3)*cos(pi/2))*sin(5*pi/12) + cos(-pi/6)*cos(5*pi/12))*sin(7*pi/12),
{
field_simp at *,
repeat {left},
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
have : ((sin((-2) * pi / 3) * cos(pi / 2) + sin(pi / 2) * cos((-2) * pi / 3)) * sin(5 * pi / 12) + cos(-pi / 6) * cos(5 * pi / 12)) * sin(7 * pi / 12) = ((sin(pi/2)*cos(-2*pi/3) + sin(-2*pi/3)*cos(pi/2))*sin(5*pi/12) + cos(-pi/6)*cos(5*pi/12))*sin(7*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = sin(-2*pi/3) * cos(pi/2) + sin(pi/2) * cos(-2*pi/3),
{
have : sin(-pi/6) = sin((-2*pi/3) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 12) * (sin(5 * pi / 12) * sin(-pi / 6) + cos(5 * pi / 12) * cos(-pi / 6)) = (sin(-pi/6)*sin(5*pi/12) + cos(-pi/6)*cos(5*pi/12))*sin(7*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/12) = sin(5*pi/12) * sin(-pi/6) + cos(5*pi/12) * cos(-pi/6),
{
have : cos(7*pi/12) = cos((5*pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12)*cos(7*pi/12) = sin(7*pi/6)/2,
{
have : sin(7*pi/6) = 2*sin(7*pi/12)*cos(7*pi/12),
{
have : sin(7*pi/6) = sin(2*(7*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(7*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_47_ZPHM_extend : (-sin(-pi/2)*sin(7*pi/6) + cos(-pi/2)*cos(7*pi/6))*cos(433*pi/6) + sqrt(3)*(1 - sin(433*pi/6)**2)=sqrt(3)/2:=
begin
have : (-sin(7 * pi / 6) * sin(-pi / 2) + cos(7 * pi / 6) * cos(-pi / 2)) * cos(433 * pi / 6) + sqrt 3 * (1 - sin(433 * pi / 6) ** 2) = (-sin(-pi/2)*sin(7*pi/6) + cos(-pi/2)*cos(7*pi/6))*cos(433*pi/6) + sqrt(3)*(1 - sin(433*pi/6)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -sin(7*pi/6) * sin(-pi/2) + cos(7*pi/6) * cos(-pi/2),
{
have : cos(2*pi/3) = cos((7*pi/6) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2 * pi / 3) * cos(433 * pi / 6) + sqrt 3 * (1 - sin(433 * pi / 6) ** 2) = cos(2*pi/3)*cos(433*pi/6) + sqrt(3)*(1 - sin(433*pi/6)**2),
{
field_simp at *,
},
have : cos(433*pi/6) ** 2 = 1 - sin(433*pi/6) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * cos(433 * pi / 6) ** 2 + cos(433 * pi / 6) * cos(2 * pi / 3) = cos(2*pi/3)*cos(433*pi/6) + sqrt(3)*cos(433*pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = cos(433*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_48_WTBU_extend : -3*cos(-158*pi/9) + 4*cos(-158*pi/9)**3=-1/2:=
begin
have : (-3) * cos((-158) * pi / 9) + 4 * cos((-158) * pi / 9) ** 3 = -3*cos(-158*pi/9) + 4*cos(-158*pi/9)**3,
{
field_simp at *,
},
have : cos(-230*pi/9) = cos(-158*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (-230*pi/9) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-3) * cos((-230) * pi / 9) + 4 * cos((-230) * pi / 9) ** 3 = -3*cos(-230*pi/9) + 4*cos(-230*pi/9)**3,
{
field_simp at *,
},
have : cos(2012*pi/9) = cos(-230*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2012*pi/9) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * cos(2012 * pi / 9) ** 3 - 3 * cos(2012 * pi / 9) = -3*cos(2012*pi/9) + 4*cos(2012*pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2012*pi/3) = 4 * cos(2012*pi/9) ** 3 - 3 * cos(2012*pi/9),
{
have : cos(2012*pi/3) = cos(3*(2012*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(2012*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2012*pi/3) (335),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_0_49_XRDQ_extend : sin(pi/12)*cos(5*pi/4) + sin(607*pi/12)*cos(335*pi/4)=1/2:=
begin
have : sin(pi / 12) * cos(5 * pi / 4) + cos(335 * pi / 4) * sin(607 * pi / 12) = sin(pi/12)*cos(5*pi/4) + sin(607*pi/12)*cos(335*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(335*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * cos(5 * pi / 4) - sin(pi / 4) * -sin(607 * pi / 12) = sin(pi/12)*cos(5*pi/4) + sin(pi/4)*sin(607*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(899*pi/12) = -sin(607*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (899*pi/12) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * cos(5 * pi / 4) + sin(pi / 4) * -cos(899 * pi / 12) = sin(pi/12)*cos(5*pi/4) - sin(pi/4)*cos(899*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(899*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*cos(5*pi/4) = sin(4*pi/3)/2 - sin(7*pi/6)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((5*pi/4) + (pi/12)) = sin(4*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((5*pi/4) - (pi/12)) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(pi/4)*cos(pi/12) = sin(pi/6)/2 + sin(pi/3)/2,
{
rw sin_mul_cos,
have : sin((pi/4) + (pi/12)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/4) - (pi/12)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(4*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_50_KHCO_extend : cos(-pi/2)*cos(3*pi/4)/2 + cos(pi/4)/2 - sin(-pi/2)*sin(3*pi/4)/2=sqrt(2)/2:=
begin
have : (-1) / 2 + cos(-pi / 2) * cos(3 * pi / 4) / 2 - sin(-pi / 2) * sin(3 * pi / 4) / 2 + (cos(pi / 4) / 2 + 1 / 2) = cos(-pi/2)*cos(3*pi/4)/2 + cos(pi/4)/2 - sin(-pi/2)*sin(3*pi/4)/2,
{
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
conv {to_lhs, rw ← this,},
have : (-1) / 2 + (-sin(3 * pi / 4) * sin(-pi / 2) + cos(3 * pi / 4) * cos(-pi / 2)) / 2 + cos(pi / 8) ** 2 = -1/2 + cos(-pi/2)*cos(3*pi/4)/2 - sin(-pi/2)*sin(3*pi/4)/2 + cos(pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(3*pi/4) * sin(-pi/2) + cos(3*pi/4) * cos(-pi/2),
{
have : cos(pi/4) = cos((3*pi/4) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 / 2 - cos(pi / 4) / 2) + cos(pi / 8) ** 2 = -1/2 + cos(pi/4)/2 + cos(pi/8)**2,
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : -sin(pi/8)**2 + cos(pi/8)**2 = cos(pi/4),
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
rw cos_pi_div_four,
end


lemma Trigo_1_51_RTSR_extend : cos(3*pi) - cos(-11*pi/6)**2 - cos(116*pi/3)**2 + (-sin(-pi)*cos(11*pi/3) + sin(11*pi/3)*cos(-pi))**2 + sin(116*pi/3)**2 + tan(5*pi/4)=1/2:=
begin
have : cos(3 * pi) - cos((-11) * pi / 6) ** 2 - cos(116 * pi / 3) ** 2 + (sin(11 * pi / 3) * cos(-pi) - sin(-pi) * cos(11 * pi / 3)) ** 2 + sin(116 * pi / 3) ** 2 + tan(5 * pi / 4) = cos(3*pi) - cos(-11*pi/6)**2 - cos(116*pi/3)**2 + (-sin(-pi)*cos(11*pi/3) + sin(11*pi/3)*cos(-pi))**2 + sin(116*pi/3)**2 + tan(5*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(14*pi/3) = sin(11*pi/3) * cos(-pi) - sin(-pi) * cos(11*pi/3),
{
have : sin(14*pi/3) = sin((11*pi/3) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3 * pi) - cos((-11) * pi / 6) ** 2 - (-sin(116 * pi / 3) ** 2 + cos(116 * pi / 3) ** 2) + sin(14 * pi / 3) ** 2 + tan(5 * pi / 4) = cos(3*pi) - cos(-11*pi/6)**2 - cos(116*pi/3)**2 + sin(14*pi/3)**2 + sin(116*pi/3)**2 + tan(5*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(232*pi/3) = -sin(116*pi/3) ** 2 + cos(116*pi/3) ** 2,
{
have : cos(232*pi/3) = cos(2*(116*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(232 * pi / 3) + sin(14 * pi / 3) ** 2 - cos((-11) * pi / 6) ** 2 + cos(3 * pi) + tan(5 * pi / 4) = cos(3*pi) - cos(-11*pi/6)**2 - cos(232*pi/3) + sin(14*pi/3)**2 + tan(5*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-7*pi/6) = -cos(232*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-7*pi/6) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi) = cos(pi),
{
rw cos_eq_cos_add_int_mul_two_pi (3*pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi,
have : cos(-11*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (-11*pi/6) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
have : sin(-7*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
have : sin(14*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (14*pi/3) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
have : tan(5*pi/4) = tan(pi/4),
{
rw tan_eq_tan_add_int_mul_pi (5*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_1_52_HPRI_extend : sin(x - 319*pi/4)**2 + cos(-2*x + pi/2)/2 - 1/2=sin(2*x):=
begin
have : -(1 / 2 - cos((-2) * x + pi / 2) / 2) + sin(x - 319 * pi / 4) ** 2 = sin(x - 319*pi/4)**2 + cos(-2*x + pi/2)/2 - 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/4) ** 2 = 1 / 2 - cos(-2*x + pi/2) / 2,
{
have : cos(-2*x + pi/2) = cos(2*(-x + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(-x + pi / 4) ** 2 + (-sin(x - 319 * pi / 4)) ** 2 = -sin(-x + pi/4)**2 + sin(x - 319*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 605*pi/4) = -sin(x - 319*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 605*pi/4) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(-x + pi / 4) ** 2 + (-cos(-x + 605 * pi / 4)) ** 2 = -sin(-x + pi/4)**2 + cos(-x + 605*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + pi/4) = -cos(-x + 605*pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-x + pi/4) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(-x + pi/4)**2 + cos(-x + pi/4)**2 = cos(-2*x + pi/2),
{
have : cos(-2*x + pi/2) = cos(2*(-x + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : cos(-2*x + pi/2) = sin(2*x),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
end


lemma Trigo_1_53_VEOJ_extend : -cos(5*pi/12)*cos(665*pi/12) + 2*cos(pi/12)*cos(7*pi/24)*cos(4709*pi/24)=1:=
begin
have : -cos(665 * pi / 12) * cos(5 * pi / 12) + 2 * cos(pi / 12) * cos(7 * pi / 24) * cos(4709 * pi / 24) = -cos(5*pi/12)*cos(665*pi/12) + 2*cos(pi/12)*cos(7*pi/24)*cos(4709*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(665*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * cos(5 * pi / 12) + 2 * cos(4709 * pi / 24) * cos(pi / 12) * cos(7 * pi / 24) = sin(pi/12)*cos(5*pi/12) + 2*cos(pi/12)*cos(7*pi/24)*cos(4709*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/24) = cos(4709*pi/24),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/24) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * cos(5 * pi / 12) + 2 * sin(7 * pi / 24) * cos(7 * pi / 24) * cos(pi / 12) = sin(pi/12)*cos(5*pi/12) + 2*sin(7*pi/24)*cos(pi/12)*cos(7*pi/24),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) = 2 * sin(7*pi/24) * cos(7*pi/24),
{
have : sin(7*pi/12) = sin(2*(7*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) = sin(5*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12) = sin(pi/2),
{
have : sin(pi/2) = sin((pi/12) + (5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_two,
end


lemma Trigo_1_54_UBZX_extend : (sin(-pi/12)*cos(-pi/2) - sin(-pi/2)*cos(-pi/12))*(-4*cos(2215*pi/36)**3 + 3*cos(2215*pi/36))=1/4:=
begin
have : -((-3) * cos(2215 * pi / 36) + 4 * cos(2215 * pi / 36) ** 3) * (sin(-pi / 12) * cos(-pi / 2) - sin(-pi / 2) * cos(-pi / 12)) = (sin(-pi/12)*cos(-pi/2) - sin(-pi/2)*cos(-pi/12))*(-4*cos(2215*pi/36)**3 + 3*cos(2215*pi/36)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = sin(-pi/12) * cos(-pi/2) - sin(-pi/2) * cos(-pi/12),
{
have : sin(5*pi/12) = sin((-pi/12) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 12) * (4 * cos(2215 * pi / 36) ** 3 - 3 * cos(2215 * pi / 36)) = -(-3*cos(2215*pi/36) + 4*cos(2215*pi/36)**3)*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2215*pi/12) = 4 * cos(2215*pi/36) ** 3 - 3 * cos(2215*pi/36),
{
have : cos(2215*pi/12) = cos(3*(2215*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 12) * -cos(2215 * pi / 12) = -sin(5*pi/12)*cos(2215*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = -cos(2215*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/12) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12)*cos(5*pi/12) = sin(5*pi/6)/2,
{
have : sin(5*pi/6) = 2*sin(5*pi/12)*cos(5*pi/12),
{
have : sin(5*pi/6) = sin(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_1_55_EVNG_extend : -2*sin(pi/2)*cos(351*pi/2) + 1 + sin(289*pi/2)=2:=
begin
have : 2 * sin(pi / 2) * -cos(351 * pi / 2) + 1 + sin(289 * pi / 2) = -2*sin(pi/2)*cos(351*pi/2) + 1 + sin(289*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(47*pi/2) = -cos(351*pi/2),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (47*pi/2) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 2) * cos(47 * pi / 2) + 1 - -sin(289 * pi / 2) = 2*sin(pi/2)*cos(47*pi/2) + 1 + sin(289*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = -sin(289*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 2) * cos(47 * pi / 2) - cos(pi) + 1 = 2*sin(pi/2)*cos(47*pi/2) + 1 - cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/2) = cos(47*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_pi_div_two,
rw cos_pi_div_two,
rw cos_pi,
norm_num,
end


lemma Trigo_1_56_KHUD_extend : -sin(pi/6)*cos(3499*pi/12) + cos(pi/6)*cos(2113*pi/12)=sqrt(2)/2:=
begin
have : -sin(pi / 6) * cos(3499 * pi / 12) + cos(2113 * pi / 12) * cos(pi / 6) = -sin(pi/6)*cos(3499*pi/12) + cos(pi/6)*cos(2113*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = cos(2113*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1105*pi/12) = cos(3499*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (1105*pi/12) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(1105*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/6)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/6) = sin(pi/4),
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
rw this,
rw sin_pi_div_four,
end


lemma Trigo_1_57_DCGU_extend : tan(1129*pi/12)=2-sqrt(3):=
begin
have : tan(493*pi/12) = tan(1129*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (493*pi/12) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(205*pi/12) = tan(493*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (205*pi/12) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = tan(205*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (pi/12) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_pi_div_twelve,
end


lemma Trigo_1_58_WSSW_extend : cos(-167*pi/180)*cos(2207*pi/180) + cos(43*pi/180)*cos(77*pi/180)=-1/2:=
begin
have : cos(2207 * pi / 180) * cos((-167) * pi / 180) + cos(43 * pi / 180) * cos(77 * pi / 180) = cos(-167*pi/180)*cos(2207*pi/180) + cos(43*pi/180)*cos(77*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi/180) = cos(2207*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (43*pi/180) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 * (2 * sin(43 * pi / 180) * cos((-167) * pi / 180)) + cos(43 * pi / 180) * cos(77 * pi / 180) = sin(43*pi/180)*cos(-167*pi/180) + cos(43*pi/180)*cos(77*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-31*pi/45) + sin(7*pi/6) = 2 * sin(43*pi/180) * cos(-167*pi/180),
{
rw sin_add_sin,
have : sin(((-31*pi/45) + (7*pi/6))/2) = sin(43*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((-31*pi/45) - (7*pi/6))/2) = cos(-167*pi/180),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 1/2*(sin(-31*pi/45) + sin(7*pi/6)) + cos(43*pi/180)*cos(77*pi/180) = sin(-31*pi/45)/2+sin(7*pi/6)/2+cos(43*pi/180)*cos(77*pi/180),
{
ring,
},
conv {to_lhs, rw this,},
have : sin((-31) * pi / 45) / 2 + sin(7 * pi / 6) / 2 + cos(43 * pi / 180) * cos(77 * pi / 180) = sin(-31*pi/45)/2 + sin(7*pi/6)/2 + cos(43*pi/180)*cos(77*pi/180),
{
field_simp at *,
},
have : sin(43*pi/180) * cos(167*pi/180) = sin(-31*pi/45) / 2 + sin(7*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((43*pi/180) + (167*pi/180)) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((43*pi/180) - (167*pi/180)) = sin(-31*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(43*pi/180) * cos(167*pi/180)) = sin(43*pi/180)*cos(167*pi/180),
{
ring,
},
have : sin(43*pi/180)*cos(167*pi/180) = -sin(31*pi/45)/2 + sin(7*pi/6)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((167*pi/180) + (43*pi/180)) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((167*pi/180) - (43*pi/180)) = sin(31*pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(43*pi/180)*cos(77*pi/180) = cos(2*pi/3)/2 + cos(-17*pi/90)/2,
{
rw cos_mul_cos,
have : cos((43*pi/180) + (77*pi/180)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((43*pi/180) - (77*pi/180)) = cos(-17*pi/90),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-17*pi/90) = cos(17*pi/90),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-17*pi/90) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(31*pi/45) = cos(17*pi/90),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (31*pi/45) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_59_IJYR_extend : -4*cos(-pi)*cos(4*pi/3) + 2*cos(2*pi/3) + 4*sin(-pi)*sin(4*pi/3) + (4*cos(559*pi/18)**3 - 3*cos(559*pi/18))**2=-9/4:=
begin
have : (-4) * cos(-pi) * cos(4 * pi / 3) + 2 * cos(2 * pi / 3) + 4 * sin(-pi) * sin(4 * pi / 3) + (4 * cos(559 * pi / 18) ** 3 - 3 * cos(559 * pi / 18)) ** 2 = -4*cos(-pi)*cos(4*pi/3) + 2*cos(2*pi/3) + 4*sin(-pi)*sin(4*pi/3) + (4*cos(559*pi/18)**3 - 3*cos(559*pi/18))**2,
{
field_simp at *,
},
have : cos(559*pi/6) = 4 * cos(559*pi/18) ** 3 - 3 * cos(559*pi/18),
{
have : cos(559*pi/6) = cos(3*(559*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : (-4) * (-sin(4 * pi / 3) * sin(-pi) + cos(4 * pi / 3) * cos(-pi)) + 2 * cos(2 * pi / 3) + cos(559 * pi / 6) ** 2 = -4*cos(-pi)*cos(4*pi/3) + 2*cos(2*pi/3) + 4*sin(-pi)*sin(4*pi/3) + cos(559*pi/6)**2,
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
have : (-cos(559 * pi / 6)) ** 2 - 4 * cos(pi / 3) + 2 * cos(2 * pi / 3) = -4*cos(pi/3) + 2*cos(2*pi/3) + cos(559*pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(559*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
end


lemma Trigo_1_60_UGOJ_extend (h0 : sin(5*pi/24)≠ 0) (h1 : (2*sin(5*pi/24))≠ 0) (h2 : (4*sin(5*pi/24)**2)≠ 0) : (-sin(5*pi/24)**2 + (1/2 - cos(5*pi/6)/2)/(4*sin(5*pi/24)**2))*sin(5*pi/12)=1/4:=
begin
have : sin(5*pi/12) ** 2 = 1 / 2 - cos(5*pi/6) / 2,
{
have : cos(5*pi/6) = cos(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(5 * pi / 24) ** 2 + (sin(5 * pi / 12) / (2 * sin(5 * pi / 24))) ** 2) * sin(5 * pi / 12) = (-sin(5*pi/24)**2 + sin(5*pi/12)**2/(4*sin(5*pi/24)**2))*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/24) = sin(5*pi/12) / ( 2 * sin(5*pi/24) ),
{
have : sin(5*pi/12) = sin(2*(5*pi/24)),
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
have : sin(5 * pi / 12) * (-sin(5 * pi / 24) ** 2 + cos(5 * pi / 24) ** 2) = (-sin(5*pi/24)**2 + cos(5*pi/24)**2)*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = -sin(5*pi/24) ** 2 + cos(5*pi/24) ** 2,
{
have : cos(5*pi/12) = cos(2*(5*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12)*cos(5*pi/12) = sin(5*pi/6)/2,
{
have : sin(5*pi/6) = 2*sin(5*pi/12)*cos(5*pi/12),
{
have : sin(5*pi/6) = sin(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_1_61_AKBN_extend : sin(pi/12)*sin(485*pi/4) + (-sin(-pi)*sin(277*pi/4) + cos(-pi)*cos(277*pi/4))*cos(pi/12)=1/2:=
begin
have : sin(pi / 12) * sin(485 * pi / 4) + cos(pi / 12) * (-sin(277 * pi / 4) * sin(-pi) + cos(277 * pi / 4) * cos(-pi)) = sin(pi/12)*sin(485*pi/4) + (-sin(-pi)*sin(277*pi/4) + cos(-pi)*cos(277*pi/4))*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(273*pi/4) = -sin(277*pi/4) * sin(-pi) + cos(277*pi/4) * cos(-pi),
{
have : cos(273*pi/4) = cos((277*pi/4) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) * -sin(485 * pi / 4) + cos(pi / 12) * cos(273 * pi / 4) = sin(pi/12)*sin(485*pi/4) + cos(pi/12)*cos(273*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(485*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) * cos(pi / 4) + cos(273 * pi / 4) * cos(pi / 12) = -sin(pi/12)*cos(pi/4) + cos(pi/12)*cos(273*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(273*pi/4),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/12)*cos(pi/4) + sin(pi/4)*cos(pi/12) = sin(pi/6),
{
have : sin(pi/6) = sin((pi/4) - (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_1_62_ZDQM_extend : -2*sin(1691*pi/24)*cos(-1187*pi/24)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12)=1:=
begin
have : 2 * sin(1691 * pi / 24) * cos(5 * pi / 12) * -cos((-1187) * pi / 24) + sin(5 * pi / 12) * cos(pi / 12) = -2*sin(1691*pi/24)*cos(-1187*pi/24)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1691*pi/24) = -cos(-1187*pi/24),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (1691*pi/24) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(1691 * pi / 24) * cos(1691 * pi / 24) * cos(5 * pi / 12) + sin(5 * pi / 12) * cos(pi / 12) = 2*sin(1691*pi/24)*cos(5*pi/12)*cos(1691*pi/24) + sin(5*pi/12)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1691*pi/12) = 2 * sin(1691*pi/24) * cos(1691*pi/24),
{
have : sin(1691*pi/12) = sin(2*(1691*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(1691*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12) = sin(pi/2),
{
have : sin(pi/2) = sin((pi/12) + (5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_two,
end


lemma Trigo_1_63_BYVR_extend : (-sin(-5*pi/6)*sin(pi) + cos(-11*pi/6)/2 + cos(pi/6)/2)*sin(-3*pi) - sin(pi/6)*cos(-3*pi)=1/2:=
begin
have : (-sin((-5) * pi / 6) * sin(pi) + (cos((-11) * pi / 6) / 2 + cos(pi / 6) / 2)) * sin((-3) * pi) - sin(pi / 6) * cos((-3) * pi) = (-sin(-5*pi/6)*sin(pi) + cos(-11*pi/6)/2 + cos(pi/6)/2)*sin(-3*pi) - sin(pi/6)*cos(-3*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/6) * cos(pi) = cos(-11*pi/6) / 2 + cos(pi/6) / 2,
{
rw cos_mul_cos,
have : cos((-5*pi/6) + (pi)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-5*pi/6) - (pi)) = cos(-11*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(-5*pi/6) * cos(pi)) = cos(-5*pi/6)*cos(pi),
{
ring,
},
have : sin((-3) * pi) * (-sin((-5) * pi / 6) * sin(pi) + cos((-5) * pi / 6) * cos(pi)) - sin(pi / 6) * cos((-3) * pi) = (-sin(-5*pi/6)*sin(pi) + cos(-5*pi/6)*cos(pi))*sin(-3*pi) - sin(pi/6)*cos(-3*pi),
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
have : sin((-3) * pi) * cos(pi / 6) - sin(pi / 6) * cos((-3) * pi) = sin(-3*pi)*cos(pi/6) - sin(pi/6)*cos(-3*pi),
{
field_simp at *,
},
have : sin(-19*pi/6) = sin(-3*pi) * cos(pi/6) - sin(pi/6) * cos(-3*pi),
{
have : sin(-19*pi/6) = sin((-3*pi) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-19*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-19*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_1_64_CZTJ_extend : -sin(0) + cos(-65*pi/3)=1/2:=
begin
have : -sin(0) - -cos((-65) * pi / 3) = -sin(0) + cos(-65*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(344*pi/3) = -cos(-65*pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (344*pi/3) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(0) + -cos(344 * pi / 3) = -sin(0) - cos(344*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -cos(344*pi/3),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/6) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (-sin(0) / 2 + sin(pi / 6) / 2) = -sin(0) + sin(pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) * cos(pi/12) = -sin(0) / 2 + sin(pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/12) + (pi/12)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/12) - (pi/12)) = sin(0),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*(sin(pi/12) * cos(pi/12)) = 2*sin(pi/12)*cos(pi/12),
{
ring,
},
conv {to_lhs, rw this,},
have : 2*sin(pi/12)*cos(pi/12) = sin(pi/6),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_1_65_RFIG_extend : tan(-pi/3) + sin(-pi/3) - sin(641*pi/4)*cos(-2*pi) + sin(-2*pi)*cos(641*pi/4) + tan(4*pi/3)=-(sqrt(2)+sqrt(3))/2:=
begin
have : tan(-pi / 3) + sin(-pi / 3) - (sin(641 * pi / 4) * cos((-2) * pi) - sin((-2) * pi) * cos(641 * pi / 4)) + tan(4 * pi / 3) = tan(-pi/3) + sin(-pi/3) - sin(641*pi/4)*cos(-2*pi) + sin(-2*pi)*cos(641*pi/4) + tan(4*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(649*pi/4) = sin(641*pi/4) * cos(-2*pi) - sin(-2*pi) * cos(641*pi/4),
{
have : sin(649*pi/4) = sin((641*pi/4) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(345*pi/4) = sin(649*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (345*pi/4) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 3) + -sin(345 * pi / 4) + tan(-pi / 3) + tan(4 * pi / 3) = tan(-pi/3) + sin(-pi/3) - sin(345*pi/4) + tan(4*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/4) = -sin(345*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/4) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_three,
have : sin(-pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
have : cos(5*pi/4) = -cos(pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
have : tan(4*pi/3) = tan(pi/3),
{
rw tan_eq_tan_add_int_mul_pi (4*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_three,
norm_num,
field_simp,
end


lemma Trigo_1_66_WMAT_extend : -(sin(-pi/9)*cos(pi/6) + sin(pi/6)*cos(-pi/9))*sin(1556*pi/9) - sin(2909*pi/18)*cos(pi/18)=sqrt(3)/2:=
begin
have : sin(pi/18) = sin(-pi/9) * cos(pi/6) + sin(pi/6) * cos(-pi/9),
{
have : sin(pi/18) = sin((-pi/9) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 18) * sin(1556 * pi / 9) + cos(pi / 18) * -sin(2909 * pi / 18) = -sin(pi/18)*sin(1556*pi/9) - sin(2909*pi/18)*cos(pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -sin(2909*pi/18),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(1556*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/18)*sin(pi/9) = -cos(pi/18)/2 + cos(pi/6)/2,
{
have : sin(pi/18)*sin(pi/9) = cos(pi/18)/2 - cos(pi/6)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((pi/9) + (pi/18)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (pi/18)) = cos(pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : cos(pi/18)*cos(pi/9) = cos(pi/6)/2 + cos(pi/18)/2,
{
rw mul_comm,
rw cos_mul_cos,
have : cos((pi/9) + (pi/18)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (pi/18)) = cos(pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw cos_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_1_67_EXPB_extend : -sin(pi)*cos(632*pi/3) - sin(632*pi/3)*cos(pi)=sqrt(3)/2:=
begin
have : -(sin(632 * pi / 3) * cos(pi) + sin(pi) * cos(632 * pi / 3)) = -sin(pi)*cos(632*pi/3) - sin(632*pi/3)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(635*pi/3) = sin(632*pi/3) * cos(pi) + sin(pi) * cos(632*pi/3),
{
have : sin(635*pi/3) = sin((632*pi/3) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(503*pi/3) = sin(635*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (503*pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-52*pi/3) = -sin(503*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-52*pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-52*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-52*pi/3) (-9),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_1_68_ZJNH_extend : -sin(13*pi/180)*cos(43*pi/180) - cos(-436*pi/3)/2 + sin(14*pi/45)/2=1/2:=
begin
have : -sin(13 * pi / 180) * cos(43 * pi / 180) - cos((-436) * pi / 3) / 2 + sin(14 * pi / 45) / 2 = -sin(13*pi/180)*cos(43*pi/180) - cos(-436*pi/3)/2 + sin(14*pi/45)/2,
{
field_simp at *,
},
have : cos(598*pi/3) = cos(-436*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (598*pi/3) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(598*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(13 * pi / 180) * cos(43 * pi / 180) + (-sin(-pi / 6) / 2 + sin(14 * pi / 45) / 2) = -sin(13*pi/180)*cos(43*pi/180) - sin(-pi/6)/2 + sin(14*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi/180) * cos(13*pi/180) = -sin(-pi/6) / 2 + sin(14*pi/45) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((13*pi/180) + (43*pi/180)) = sin(14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin((13*pi/180) - (43*pi/180)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(43*pi/180) * cos(13*pi/180)) = sin(43*pi/180)*cos(13*pi/180),
{
ring,
},
have : -sin(13*pi/180)*cos(43*pi/180) = -sin(14*pi/45)/2 + sin(pi/6)/2,
{
have : sin(13*pi/180)*cos(43*pi/180) = -sin(pi/6)/2 + sin(14*pi/45)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((43*pi/180) + (13*pi/180)) = sin(14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin((43*pi/180) - (13*pi/180)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
have : sin(43*pi/180)*cos(13*pi/180) = sin(pi/6)/2 + sin(14*pi/45)/2,
{
rw sin_mul_cos,
have : sin((43*pi/180) + (13*pi/180)) = sin(14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin((43*pi/180) - (13*pi/180)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_69_WIXQ_extend : sin(5*pi/6)*sin(565*pi/12) + (-1 + 2*(-sin(pi/24)**2 + cos(pi/24)**2)**2)*sin(5*pi/12)=sqrt(2)/2:=
begin
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
have : - -sin(565 * pi / 12) * sin(5 * pi / 6) + (-1 + 2 * cos(pi / 12) ** 2) * sin(5 * pi / 12) = sin(5*pi/6)*sin(565*pi/12) + (-1 + 2*cos(pi/12)**2)*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(565*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/12) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) * sin(5 * pi / 6) + sin(5 * pi / 12) * (2 * cos(pi / 12) ** 2 - 1) = -sin(pi/12)*sin(5*pi/6) + (-1 + 2*cos(pi/12)**2)*sin(5*pi/12),
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
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(pi/12)*sin(pi/6) + cos(pi/12)*cos(pi/6) = cos(pi/4),
{
have : cos(pi/4) = cos((pi/6) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_1_70_KZTD_extend : 3*sin(-pi/3)*cos(4*pi/9) - 4*(sin(-pi/3)*cos(4*pi/9) + sin(1103*pi/9)*cos(-pi/3))**3 + 3*sin(1103*pi/9)*cos(-pi/3)=sqrt(3)/2:=
begin
have : sin(4*pi/9) = sin(1103*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4*pi/9) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * (sin(4 * pi / 9) * cos(-pi / 3) + sin(-pi / 3) * cos(4 * pi / 9)) ** 3 + 3 * (sin(4 * pi / 9) * cos(-pi / 3) + sin(-pi / 3) * cos(4 * pi / 9)) = 3*sin(-pi/3)*cos(4*pi/9) - 4*(sin(-pi/3)*cos(4*pi/9) + sin(4*pi/9)*cos(-pi/3))**3 + 3*sin(4*pi/9)*cos(-pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(4*pi/9) * cos(-pi/3) + sin(-pi/3) * cos(4*pi/9),
{
have : sin(pi/9) = sin((4*pi/9) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
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
rw sin_pi_div_three,
end


lemma Trigo_1_71_ORDR_extend : -cos(551*pi/6)=-sqrt(3)/2:=
begin
have : sin(136*pi/3) = -cos(551*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (136*pi/3) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(443*pi/3) = sin(136*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (443*pi/3) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = sin(443*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/3) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
field_simp,
end


lemma Trigo_1_72_OIBK_extend : (4*sin(-5*pi/12)*cos(pi/2) + 4*(-3*cos(-5*pi/36) + 4*cos(-5*pi/36)**3)*cos(164*pi))*cos(pi/12)=1:=
begin
have : (4 * sin((-5) * pi / 12) * cos(pi / 2) + 4 * (4 * cos((-5) * pi / 36) ** 3 - 3 * cos((-5) * pi / 36)) * cos(164 * pi)) * cos(pi / 12) = (4*sin(-5*pi/12)*cos(pi/2) + 4*(-3*cos(-5*pi/36) + 4*cos(-5*pi/36)**3)*cos(164*pi))*cos(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/12) = 4 * cos(-5*pi/36) ** 3 - 3 * cos(-5*pi/36),
{
have : cos(-5*pi/12) = cos(3*(-5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : 4 * (sin((-5) * pi / 12) * cos(pi / 2) + cos(164 * pi) * cos((-5) * pi / 12)) * cos(pi / 12) = (4*sin(-5*pi/12)*cos(pi/2) + 4*cos(-5*pi/12)*cos(164*pi))*cos(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = cos(164*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/2) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * (sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12)) * cos(pi / 12) = 4*(sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12))*cos(pi/12),
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
have : 4*sin(pi/12)*cos(pi/12) = 2*sin(pi/6),
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_1_73_JTJS_extend : (-sin(pi/3)*cos(73*pi/180) + sin(73*pi/180)*cos(pi/3))*sin(43*pi/180) - cos(6539*pi/45)/2 + cos(875*pi/6)/2=sqrt(3)/2:=
begin
have : (sin(73 * pi / 180) * cos(pi / 3) - sin(pi / 3) * cos(73 * pi / 180)) * sin(43 * pi / 180) - cos(6539 * pi / 45) / 2 + cos(875 * pi / 6) / 2 = (-sin(pi/3)*cos(73*pi/180) + sin(73*pi/180)*cos(pi/3))*sin(43*pi/180) - cos(6539*pi/45)/2 + cos(875*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = sin(73*pi/180) * cos(pi/3) - sin(pi/3) * cos(73*pi/180),
{
have : sin(13*pi/180) = sin((73*pi/180) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 180) * sin(43 * pi / 180) - (cos(6539 * pi / 45) / 2 - cos(875 * pi / 6) / 2) = sin(13*pi/180)*sin(43*pi/180) - cos(6539*pi/45)/2 + cos(875*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(26203*pi/180) * sin(47*pi/180) = cos(6539*pi/45) / 2 - cos(875*pi/6) / 2,
{
rw sin_mul_sin,
have : cos((26203*pi/180) + (47*pi/180)) = cos(875*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((26203*pi/180) - (47*pi/180)) = cos(6539*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(26203*pi/180) * sin(47*pi/180)) = sin(47*pi/180)*sin(26203*pi/180),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(13 * pi / 180) * sin(43 * pi / 180) + sin(47 * pi / 180) * -sin(26203 * pi / 180) = sin(13*pi/180)*sin(43*pi/180) - sin(47*pi/180)*sin(26203*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/180) = -sin(26203*pi/180),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/180) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180)*sin(43*pi/180) = -cos(14*pi/45)/2 + cos(pi/6)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((43*pi/180) + (13*pi/180)) = cos(14*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : cos((43*pi/180) - (13*pi/180)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(47*pi/180)*cos(13*pi/180) = sin(17*pi/90)/2 + sin(pi/3)/2,
{
rw sin_mul_cos,
have : sin((47*pi/180) + (13*pi/180)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((47*pi/180) - (13*pi/180)) = sin(17*pi/90),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : cos(14*pi/45) = sin(17*pi/90),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (14*pi/45) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
rw sin_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_1_74_FPZB_extend : -sqrt(3)*cos(x + 133*pi/2) - cos(x + 77*pi)=2*cos(x-pi/3):=
begin
have : -sqrt 3 * cos(x + 133 * pi / 2) - cos(x + 77 * pi) = -sqrt(3)*cos(x + 133*pi/2) - cos(x + 77*pi),
{
field_simp at *,
},
have : cos(-x + 163*pi/2) = cos(x + 133*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 163*pi/2) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * -cos(-x + 163 * pi / 2) - cos(x + 77 * pi) = -sqrt(3)*cos(-x + 163*pi/2) - cos(x + 77*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -cos(-x + 163*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(x) + -cos(x + 77 * pi) = sqrt(3)*sin(x) - cos(x + 77*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -cos(x + 77*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi/3) = sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
{
have : cos(x-pi/3) = cos((x) - (pi/3)),
{
apply congr_arg,
ring,
},
rw cos_sub,
ring,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_1_75_QZGG_extend (h0 : cos(pi/3)≠ 0) (h1 : (2*cos(pi/3))≠ 0) : (sin(2*pi/3)*sin(y + pi/3)/(2*cos(pi/3)) + cos(pi/3)*cos(y + pi/3))**2*cos(x)**2 - sin(x)**2*cos(y + 247*pi/2)**2 + sin(x)**2 + cos(y + 247*pi/2)**2=1:=
begin
have : (sin(2 * pi / 3) / (2 * cos(pi / 3)) * sin(y + pi / 3) + cos(pi / 3) * cos(y + pi / 3)) ** 2 * cos(x) ** 2 - sin(x) ** 2 * cos(y + 247 * pi / 2) ** 2 + sin(x) ** 2 + cos(y + 247 * pi / 2) ** 2 = (sin(2*pi/3)*sin(y + pi/3)/(2*cos(pi/3)) + cos(pi/3)*cos(y + pi/3))**2*cos(x)**2 - sin(x)**2*cos(y + 247*pi/2)**2 + sin(x)**2 + cos(y + 247*pi/2)**2,
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
have : sin(y) = cos(y + 247*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (y) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x) ** 2 * sin(y) ** 2 + sin(x) ** 2 + sin(y) ** 2 + cos(x) ** 2 * (sin(y + pi / 3) * sin(pi / 3) + cos(y + pi / 3) * cos(pi / 3)) ** 2 = (sin(pi/3)*sin(y + pi/3) + cos(pi/3)*cos(y + pi/3))**2*cos(x)**2 - sin(x)**2*sin(y)**2 + sin(x)**2 + sin(y)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(y) = sin(y + pi/3) * sin(pi/3) + cos(y + pi/3) * cos(pi/3),
{
have : cos(y) = cos((y + pi/3) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
rw cos_sq',
rw cos_sq',
have : (1 - sin(x)**2)*(1 - sin(y)**2) = sin(x)**2*sin(y)**2 - sin(x)**2 - sin(y)**2 + 1,
{
ring_exp,
},
rw this,
norm_num,
ring_exp,
end


lemma Trigo_1_76_AHWK_extend (h0 : cos(575*pi/6)≠ 0) (h1 : cos(575*pi/6)≠ 0) (h2 : (2*cos(575*pi/6))≠ 0) : sin(575*pi/3)/cos(575*pi/6) + sin(541*pi/3)**2=-1/4:=
begin
have : 2 * (sin(575 * pi / 3) / (2 * cos(575 * pi / 6))) + sin(541 * pi / 3) ** 2 = sin(575*pi/3)/cos(575*pi/6) + sin(541*pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(575*pi/6) = sin(575*pi/3) / ( 2 * cos(575*pi/6) ),
{
have : sin(575*pi/3) = sin(2*(575*pi/6)),
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
have : sin(pi/3) = sin(541*pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/3) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 3) ** 2 + 2 * sin(575 * pi / 6) = 2*sin(575*pi/6) + sin(pi/3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = sin(575*pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/3) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
end


lemma Trigo_1_77_GUMD_extend : -1 + 2*(1 - 2*(sin(-5*pi/48)*cos(-pi/6) - sin(-pi/6)*cos(-5*pi/48))**2)**2=sqrt(2)/2:=
begin
have : -1 + 2 * (1 - 2 * (sin((-5) * pi / 48) * cos(-pi / 6) - sin(-pi / 6) * cos((-5) * pi / 48)) ** 2) ** 2 = -1 + 2*(1 - 2*(sin(-5*pi/48)*cos(-pi/6) - sin(-pi/6)*cos(-5*pi/48))**2)**2,
{
field_simp at *,
},
have : sin(pi/16) = sin(-5*pi/48) * cos(-pi/6) - sin(-pi/6) * cos(-5*pi/48),
{
have : sin(pi/16) = sin((-5*pi/48) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
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
have : 1 - 2 * (1 - cos(pi / 8) ** 2) = -1 + 2*cos(pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) ** 2 = 1 - cos(pi/8) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 1 - 2*sin(pi/8)**2 = cos(pi/4),
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
rw cos_pi_div_four,
end


lemma Trigo_1_78_LOWI_extend : 2*sin(425*pi/36)**3 + sqrt(3)*cos(1147*pi/12)/2 - 3*sin(425*pi/36)/2=sqrt(2)/2:=
begin
have : sqrt 3 * cos(1147 * pi / 12) / 2 - ((-4) * sin(425 * pi / 36) ** 3 + 3 * sin(425 * pi / 36)) / 2 = 2*sin(425*pi/36)**3 + sqrt(3)*cos(1147*pi/12)/2 - 3*sin(425*pi/36)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(425*pi/12) = -4 * sin(425*pi/36) ** 3 + 3 * sin(425*pi/36),
{
have : sin(425*pi/12) = sin(3*(425*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * cos(1147 * pi / 12) / 2 + -sin(425 * pi / 12) / 2 = sqrt(3)*cos(1147*pi/12)/2 - sin(425*pi/12)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(425*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * cos(1147 * pi / 12) / 2 + cos(pi / 12) / 2 = sqrt(3)*cos(1147*pi/12)/2 + cos(pi/12)/2,
{
field_simp at *,
},
have : sin(pi/12) = cos(1147*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3)*sin(pi/12)/2 = sin(pi/12)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/12)/2 = sin(pi/6)*cos(pi/12),
{
field_simp,
},
rw this,
have : sin(pi/12)*cos(pi/6) + sin(pi/6)*cos(pi/12) = sin(pi/4),
{
have : sin(pi/4) = sin((pi/6) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_four,
end


lemma Trigo_1_79_CUNC_extend (h0 : (2*cos(pi/3))≠ 0) (h1 : (2*(-sin(-2*pi)*sin(7*pi/3)+cos(-2*pi)*cos(7*pi/3)))≠ 0) (h2 : (2*(-sin(7*pi/3)*sin((-2)*pi)+cos(7*pi/3)*cos((-2)*pi)))≠ 0) (h3 : (-2*sin(-2*pi)*sin(7*pi/3)+cos(pi/3)+cos(13*pi/3))≠ 0) (h4 : (2*(-sin((-2)*pi)*sin(7*pi/3)+(cos(13*pi/3)/2+cos(pi/3)/2)))≠ 0) : (cos(569*pi/6) + sqrt(3)*(-sin(-2*pi)*sin(7*pi/3) + cos(pi/3)/2 + cos(13*pi/3)/2))*sin(2*pi/3)/(-2*sin(-2*pi)*sin(7*pi/3) + cos(pi/3) + cos(13*pi/3)) + 1/2=1/2:=
begin
have : (cos(569 * pi / 6) + sqrt 3 * (-sin((-2) * pi) * sin(7 * pi / 3) + (cos(13 * pi / 3) / 2 + cos(pi / 3) / 2))) * sin(2 * pi / 3) / (2 * (-sin((-2) * pi) * sin(7 * pi / 3) + (cos(13 * pi / 3) / 2 + cos(pi / 3) / 2))) + 1 / 2 = (cos(569*pi/6) + sqrt(3)*(-sin(-2*pi)*sin(7*pi/3) + cos(pi/3)/2 + cos(13*pi/3)/2))*sin(2*pi/3)/(-2*sin(-2*pi)*sin(7*pi/3) + cos(pi/3) + cos(13*pi/3)) + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/3) * cos(-2*pi) = cos(13*pi/3) / 2 + cos(pi/3) / 2,
{
rw cos_mul_cos,
have : cos((7*pi/3) + (-2*pi)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((7*pi/3) - (-2*pi)) = cos(13*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(7*pi/3) * cos(-2*pi)) = cos(-2*pi)*cos(7*pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : (cos(569 * pi / 6) + sqrt 3 * (-sin(7 * pi / 3) * sin((-2) * pi) + cos(7 * pi / 3) * cos((-2) * pi))) * sin(2 * pi / 3) / (2 * (-sin(7 * pi / 3) * sin((-2) * pi) + cos(7 * pi / 3) * cos((-2) * pi))) + 1 / 2 = (cos(569*pi/6) + sqrt(3)*(-sin(-2*pi)*sin(7*pi/3) + cos(-2*pi)*cos(7*pi/3)))*sin(2*pi/3)/(2*(-sin(-2*pi)*sin(7*pi/3) + cos(-2*pi)*cos(7*pi/3))) + 1/2,
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
have : (- -cos(569 * pi / 6) + sqrt 3 * cos(pi / 3)) * sin(2 * pi / 3) / (2 * cos(pi / 3)) + 1 / 2 = (cos(569*pi/6) + sqrt(3)*cos(pi/3))*sin(2*pi/3)/(2*cos(pi/3)) + 1/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -cos(569*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_pi_div_three,
rw cos_pi_div_three,
norm_num,
field_simp,
end


lemma Trigo_1_80_WMMO_extend : -sin(143*pi/2)*sin(707*pi/6) + cos(-107*pi/6)*cos(pi/2)=-1/2:=
begin
have : -sin(707 * pi / 6) * sin(143 * pi / 2) + cos((-107) * pi / 6) * cos(pi / 2) = -sin(143*pi/2)*sin(707*pi/6) + cos(-107*pi/6)*cos(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-107*pi/6) = -sin(707*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-107*pi/6) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin((-107) * pi / 6) * -sin(143 * pi / 2) + cos((-107) * pi / 6) * cos(pi / 2) = sin(-107*pi/6)*sin(143*pi/2) + cos(-107*pi/6)*cos(pi/2),
{
field_simp at *,
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
have : -sin((-107) * pi / 6) * sin(pi / 2) + cos((-107) * pi / 6) * cos(pi / 2) = -sin(-107*pi/6)*sin(pi/2) + cos(-107*pi/6)*cos(pi/2),
{
field_simp at *,
},
have : cos(-52*pi/3) = -sin(-107*pi/6) * sin(pi/2) + cos(-107*pi/6) * cos(pi/2),
{
have : cos(-52*pi/3) = cos((-107*pi/6) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-52*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-52*pi/3) (-9),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_1_81_RBFL_extend (h0 : cos(11*pi/8)≠ 0) (h1 : (1-tan(11*pi/8)**2)≠ 0) : 2*tan(11*pi/8)/(1 - tan(11*pi/8)**2) - sin(pi/6)**2 - sin(pi/12)*sin(pi/4) + cos(pi/6)/2 + 1/2=-1/2:=
begin
have : 2 * tan(11 * pi / 8) / (1 - tan(11 * pi / 8) ** 2) - sin(pi / 12) * sin(pi / 4) + (1 - 2 * sin(pi / 6) ** 2) / 2 + cos(pi / 6) / 2 = 2*tan(11*pi/8)/(1 - tan(11*pi/8)**2) - sin(pi/6)**2 - sin(pi/12)*sin(pi/4) + cos(pi/6)/2 + 1/2,
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
have : 2 * tan(11 * pi / 8) / (1 - tan(11 * pi / 8) ** 2) - sin(pi / 12) * sin(pi / 4) + (cos(pi / 6) / 2 + cos(pi / 3) / 2) = 2*tan(11*pi/8)/(1 - tan(11*pi/8)**2) - sin(pi/12)*sin(pi/4) + cos(pi/3)/2 + cos(pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) * cos(pi/12) = cos(pi/6) / 2 + cos(pi/3) / 2,
{
rw cos_mul_cos,
have : cos((pi/4) + (pi/12)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/4) - (pi/12)) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(pi/4) * cos(pi/12)) = cos(pi/12)*cos(pi/4),
{
ring,
},
conv {to_lhs, rw this,},
have : -sin(pi / 12) * sin(pi / 4) + cos(pi / 12) * cos(pi / 4) + 2 * tan(11 * pi / 8) / (1 - tan(11 * pi / 8) ** 2) = 2*tan(11*pi/8)/(1 - tan(11*pi/8)**2) - sin(pi/12)*sin(pi/4) + cos(pi/12)*cos(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/4) = 2 * tan(11*pi/8) / ( 1 - tan(11*pi/8) ** 2 ),
{
have : tan(11*pi/4) = tan(2*(11*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/4) = -tan(pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (11*pi/4) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(pi/12)*sin(pi/4) + cos(pi/12)*cos(pi/4) = cos(pi/3),
{
have : cos(pi/3) = cos((pi/4) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw tan_pi_div_four,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_1_82_CRYV_extend (h0 : cos(43*pi/180)≠ 0) (h1 : (2*cos(43*pi/180))≠ 0) : -sin(4351*pi/45)/2 - sin(583*pi/6)/2 + sin(43*pi/90)*cos(13*pi/180)/(2*cos(43*pi/180))=1/2:=
begin
have : -(sin(4351 * pi / 45) / 2 + sin(583 * pi / 6) / 2) + sin(43 * pi / 90) * cos(13 * pi / 180) / (2 * cos(43 * pi / 180)) = -sin(4351*pi/45)/2 - sin(583*pi/6)/2 + sin(43*pi/90)*cos(13*pi/180)/(2*cos(43*pi/180)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17447*pi/180) * cos(43*pi/180) = sin(4351*pi/45) / 2 + sin(583*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((17447*pi/180) + (43*pi/180)) = sin(583*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((17447*pi/180) - (43*pi/180)) = sin(4351*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(17447*pi/180) * cos(43*pi/180)) = -sin(17447*pi/180)*cos(43*pi/180),
{
ring,
},
conv {to_lhs, rw this,},
have : -sin(17447 * pi / 180) * cos(43 * pi / 180) + sin(43 * pi / 90) / (2 * cos(43 * pi / 180)) * cos(13 * pi / 180) = -sin(17447*pi/180)*cos(43*pi/180) + sin(43*pi/90)*cos(13*pi/180)/(2*cos(43*pi/180)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi/180) = sin(43*pi/90) / ( 2 * cos(43*pi/180) ),
{
have : sin(43*pi/90) = sin(2*(43*pi/180)),
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
have : sin(13*pi/180) = sin(17447*pi/180),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (13*pi/180) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180) = sin(pi/6),
{
have : sin(pi/6) = sin((43*pi/180) - (13*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_1_83_POFB_extend : -2*cos(73*pi/12)**2 + 2*cos(25*pi/12)**2=0:=
begin
have : (-2) * cos(73 * pi / 12) ** 2 + (2 * cos(25 * pi / 12) ** 2 - 1) + 1 = -2*cos(73*pi/12)**2 + 2*cos(25*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/6) = 2 * cos(25*pi/12) ** 2 - 1,
{
have : cos(25*pi/6) = cos(2*(25*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -(2 * cos(73 * pi / 12) ** 2 - 1) + cos(25 * pi / 6) = -2*cos(73*pi/12)**2 + cos(25*pi/6) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(73*pi/6) = 2 * cos(73*pi/12) ** 2 - 1,
{
have : cos(73*pi/6) = cos(2*(73*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-25*pi/3) = -cos(73*pi/6),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-25*pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-25*pi/3) = -sin(25*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-25*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(25*pi/3) = sin(pi/3),
{
rw sin_eq_sin_add_int_mul_two_pi (25*pi/3) (-4),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(25*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
rw cos_pi_div_six,
norm_num,
end


lemma Trigo_1_84_FSBB_extend : -4*sin(x + 169*pi/6)**3 + 3*sin(x + 169*pi/6)=-4*sin(x + 111*pi/2)**3 + 3*sin(x + 111*pi/2):=
begin
have : (-4) * sin(x + 169 * pi / 6) ** 3 + 3 * sin(x + 169 * pi / 6) = -4*sin(x + 169*pi/6)**3 + 3*sin(x + 169*pi/6),
{
field_simp at *,
},
have : sin(3*x + 169*pi/2) = -4 * sin(x + 169*pi/6) ** 3 + 3 * sin(x + 169*pi/6),
{
have : sin(3*x + 169*pi/2) = sin(3*(x + 169*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * (-sin(x + 111 * pi / 2)) ** 3 - 3 * -sin(x + 111 * pi / 2) = -4*sin(x + 111*pi/2)**3 + 3*sin(x + 111*pi/2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(x) = -sin(x + 111*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(3*x) = sin(3*x + 169*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3*x) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*x) = 4*cos(x)**3 - 3*cos(x),
{
have : cos(3*x) = cos(3*(x)),
{
apply congr_arg,
ring,
},
rw cos_three_mul,
},
rw this,
end


lemma Trigo_1_85_FJEH_extend (h0 : tan(383*pi/4)≠ 0) : -(1 - 2*sin(pi/6)**2)**2 - sin(14*pi)/tan(383*pi/4) + sin(pi/6)**2/2 + 4/tan(383*pi/4)**2=31/8:=
begin
have : -(1 - 2 * sin(pi / 6) ** 2) ** 2 + sin(14 * pi) * ((-1) / tan(383 * pi / 4)) + sin(pi / 6) ** 2 / 2 + 4 * ((-1) / tan(383 * pi / 4)) ** 2 = -(1 - 2*sin(pi/6)**2)**2 - sin(14*pi)/tan(383*pi/4) + sin(pi/6)**2/2 + 4/tan(383*pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = -1 / tan(383*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/4) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi) = sin(14*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) ** 2 / 2 + sin(pi) * tan(pi / 4) - (1 - 2 * sin(pi / 6) ** 2) ** 2 + 4 * tan(pi / 4) ** 2 = -(1 - 2*sin(pi/6)**2)**2 + sin(pi)*tan(pi/4) + sin(pi/6)**2/2 + 4*tan(pi/4)**2,
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
rw cos_pi_div_three,
rw sin_pi,
rw sin_pi_div_six,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_1_86_PKQH_extend : (-1 + 2*sin(12739*pi/90)**2)*sin(7*pi/90) + sin(19*pi/45)*sin(4954*pi/45)=1/2:=
begin
have : (-1 + 2 * (-sin(12739 * pi / 90)) ** 2) * sin(7 * pi / 90) + sin(19 * pi / 45) * sin(4954 * pi / 45) = (-1 + 2*sin(12739*pi/90)**2)*sin(7*pi/90) + sin(19*pi/45)*sin(4954*pi/45),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/45) = -sin(12739*pi/90),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/45) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 90) * (2 * cos(2 * pi / 45) ** 2 - 1) + sin(19 * pi / 45) * sin(4954 * pi / 45) = (-1 + 2*cos(2*pi/45)**2)*sin(7*pi/90) + sin(19*pi/45)*sin(4954*pi/45),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/45) = 2 * cos(2*pi/45) ** 2 - 1,
{
have : cos(4*pi/45) = cos(2*(2*pi/45)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(37*pi/90) = sin(4954*pi/45),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (37*pi/90) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/90)*cos(4*pi/45) = -sin(pi/90)/2 + sin(pi/6)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((4*pi/45) + (7*pi/90)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((4*pi/45) - (7*pi/90)) = sin(pi/90),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(19*pi/45)*cos(37*pi/90) = sin(pi/90)/2 + sin(5*pi/6)/2,
{
rw sin_mul_cos,
have : sin((19*pi/45) + (37*pi/90)) = sin(5*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((19*pi/45) - (37*pi/90)) = sin(pi/90),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_87_WXUN_extend (h0 : cos(-2*pi/3)≠ 0) (h1 : tan(62*pi/3)≠ 0) (h2 : cos((-2)*pi/3)≠ 0) (h3 : cos(130*pi/3)≠ 0) : (-sin(pi/2)*cos(7*pi/4) + 1/tan(62*pi/3) + sin(7*pi/4)*cos(pi/2))/cos(130*pi/3)=(3*sqrt(2)+2*sqrt(3))/3:=
begin
have : (sin(7 * pi / 4) * cos(pi / 2) - sin(pi / 2) * cos(7 * pi / 4) + 1 / tan(62 * pi / 3)) / cos(130 * pi / 3) = (-sin(pi/2)*cos(7*pi/4) + 1/tan(62*pi/3) + sin(7*pi/4)*cos(pi/2))/cos(130*pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/4) = sin(7*pi/4) * cos(pi/2) - sin(pi/2) * cos(7*pi/4),
{
have : sin(5*pi/4) = sin((7*pi/4) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi/3) = cos(130*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi/3) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(5 * pi / 4) + 1 / tan(62 * pi / 3)) / cos((-2) * pi / 3) = (sin(5*pi/4) + 1/tan(62*pi/3))/cos(-2*pi/3),
{
field_simp at *,
},
have : tan(11*pi/6) = 1 / tan(62*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (11*pi/6) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/4) = -sin(pi/4),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(11*pi/6) = -tan(pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (11*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_four,
rw tan_pi_div_six,
rw cos_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_1_88_PLZO_extend : (-1 + 2*cos(25*pi/4)**2)*cos(337*pi/2)=0:=
begin
have : sin(5*pi) = cos(337*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi) * (2 * cos(25 * pi / 4) ** 2 - 1) = (-1 + 2*cos(25*pi/4)**2)*sin(5*pi),
{
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/2) = 2 * cos(25*pi/4) ** 2 - 1,
{
have : cos(25*pi/2) = cos(2*(25*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/2) = cos(25*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (3*pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi) = sin(pi),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi,
norm_num,
end


lemma Trigo_1_89_VSEE_extend (h0 : (1-(sin(5*pi/6)/cos(5*pi/6))**2)≠ 0) (h1 : cos(5*pi/6)≠ 0) (h2 : ((-sin(5*pi/6)**2/cos(5*pi/6)**2+1)*cos(5*pi/6))≠ 0) (h3 : sin(5*pi/6)≠ 0) (h4 : (sin(5*pi/3)/(2*sin(5*pi/6)))≠ 0) (h5 : ((-4*sin(5*pi/6)**4/sin(5*pi/3)**2+1)*sin(5*pi/3))≠ 0) (h6 : sin(5*pi/3)≠ 0) (h7 : ((-sin(5*pi/6)**2/(sin(5*pi/3)/(2*sin(5*pi/6)))**2+1)*(sin(5*pi/3)/(2*sin(5*pi/6))))≠ 0) (h8 : (2*sin(5*pi/6))≠ 0) (h9 : (((-4)*sin(5*pi/6)**4/sin(5*pi/3)**2+1)*sin(5*pi/3))≠ 0) : 4*(1 - cos(5*pi/6)**2)/((-4*sin(5*pi/6)**4/sin(5*pi/3)**2 + 1)*sin(5*pi/3))=-sqrt(3):=
begin
have : 4 * (1 - cos(5 * pi / 6) ** 2) / (((-4) * sin(5 * pi / 6) ** 4 / sin(5 * pi / 3) ** 2 + 1) * sin(5 * pi / 3)) = 4*(1 - cos(5*pi/6)**2)/((-4*sin(5*pi/6)**4/sin(5*pi/3)**2 + 1)*sin(5*pi/3)),
{
field_simp at *,
},
have : sin(5*pi/6) ** 2 = 1 - cos(5*pi/6) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(5 * pi / 6) / ((-sin(5 * pi / 6) ** 2 / (sin(5 * pi / 3) / (2 * sin(5 * pi / 6))) ** 2 + 1) * (sin(5 * pi / 3) / (2 * sin(5 * pi / 6)))) = 4*sin(5*pi/6)**2/((-4*sin(5*pi/6)**4/sin(5*pi/3)**2 + 1)*sin(5*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : 2 * (sin(5 * pi / 6) / cos(5 * pi / 6)) / (1 - (sin(5 * pi / 6) / cos(5 * pi / 6)) ** 2) = 2*sin(5*pi/6)/((-sin(5*pi/6)**2/cos(5*pi/6)**2 + 1)*cos(5*pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/6) = sin(5*pi/6) / cos(5*pi/6),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/6) = -tan(pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (5*pi/6) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_90_GKCK_extend : -sin(988*pi/5)*cos(1393*pi/30) + (-sin(pi/30)**2 + cos(pi/30)**2)*sin(pi/10)=1/2:=
begin
have : -cos(1393 * pi / 30) * sin(988 * pi / 5) + (-sin(pi / 30) ** 2 + cos(pi / 30) ** 2) * sin(pi / 10) = -sin(988*pi/5)*cos(1393*pi/30) + (-sin(pi/30)**2 + cos(pi/30)**2)*sin(pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/15) = cos(1393*pi/30),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/15) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 15) * sin(988 * pi / 5) + sin(pi / 10) * (-sin(pi / 30) ** 2 + cos(pi / 30) ** 2) = -sin(pi/15)*sin(988*pi/5) + (-sin(pi/30)**2 + cos(pi/30)**2)*sin(pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/15) = -sin(pi/30) ** 2 + cos(pi/30) ** 2,
{
have : cos(pi/15) = cos(2*(pi/30)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 15) * -sin(988 * pi / 5) + sin(pi / 10) * cos(pi / 15) = -sin(pi/15)*sin(988*pi/5) + sin(pi/10)*cos(pi/15),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/10) = -sin(988*pi/5),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/10) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/15)*cos(pi/10) = -sin(pi/30)/2 + sin(pi/6)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/10) + (pi/15)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/10) - (pi/15)) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(pi/10)*cos(pi/15) = sin(pi/30)/2 + sin(pi/6)/2,
{
rw sin_mul_cos,
have : sin((pi/10) + (pi/15)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/10) - (pi/15)) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_91_PNLW_extend : (sin(13*pi/20)*cos(pi/2) - sin(pi/2)*cos(13*pi/20))*cos(2447*pi/20) + (-1 + 2*cos(3*pi/40)**2)*sin(7*pi/20)=1:=
begin
have : sin(3*pi/20) = sin(13*pi/20) * cos(pi/2) - sin(pi/2) * cos(13*pi/20),
{
have : sin(3*pi/20) = sin((13*pi/20) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3 * pi / 20) * cos(2447 * pi / 20) + sin(7 * pi / 20) * (2 * cos(3 * pi / 40) ** 2 - 1) = sin(3*pi/20)*cos(2447*pi/20) + (-1 + 2*cos(3*pi/40)**2)*sin(7*pi/20),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/20) = 2 * cos(3*pi/40) ** 2 - 1,
{
have : cos(3*pi/20) = cos(2*(3*pi/40)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/20) = cos(2447*pi/20),
{
rw cos_eq_cos_add_int_mul_two_pi (7*pi/20) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/20)*cos(7*pi/20) + sin(7*pi/20)*cos(3*pi/20) = sin(pi/2),
{
have : sin(pi/2) = sin((3*pi/20) + (7*pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_two,
end


lemma Trigo_1_92_REXZ_extend : -sin(19*pi/180)*sin(13*pi/90) + sin(-7*pi/4)/2 - cos(6653*pi/180)/2=sqrt(2)/2:=
begin
have : -sin(19 * pi / 180) * sin(13 * pi / 90) + sin((-7) * pi / 4) / 2 + -cos(6653 * pi / 180) / 2 = -sin(19*pi/180)*sin(13*pi/90) + sin(-7*pi/4)/2 - cos(6653*pi/180)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(457*pi/180) = -cos(6653*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (457*pi/180) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(19 * pi / 180) * sin(13 * pi / 90) + (sin((-7) * pi / 4) / 2 + sin(457 * pi / 180) / 2) = -sin(19*pi/180)*sin(13*pi/90) + sin(-7*pi/4)/2 + sin(457*pi/180)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(71*pi/180) * cos(193*pi/90) = sin(-7*pi/4) / 2 + sin(457*pi/180) / 2,
{
rw sin_mul_cos,
have : sin((71*pi/180) + (193*pi/90)) = sin(457*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : sin((71*pi/180) - (193*pi/90)) = sin(-7*pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(71*pi/180) * cos(193*pi/90)) = sin(71*pi/180)*cos(193*pi/90),
{
ring,
},
have : cos(13*pi/90) = cos(193*pi/90),
{
rw cos_eq_cos_add_int_mul_two_pi (13*pi/90) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(71*pi/180) = cos(19*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (71*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(19*pi/180)*sin(13*pi/90) + cos(19*pi/180)*cos(13*pi/90) = cos(pi/4),
{
have : cos(pi/4) = cos((13*pi/90) + (19*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_1_93_TSCF_extend : (-3*cos(pi/36) + 3*sin(2137*pi/36) - 4*sin(2137*pi/36)**3 + 4*cos(pi/36)**3)*(-3*cos(pi/36) + 4*sin(2137*pi/36)**3 - 3*sin(2137*pi/36) + 4*cos(pi/36)**3)=sqrt(3)/2:=
begin
have : (3 * sin(2137 * pi / 36) + (4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36)) - 4 * sin(2137 * pi / 36) ** 3) * (4 * sin(2137 * pi / 36) ** 3 + (4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36)) - 3 * sin(2137 * pi / 36)) = (-3*cos(pi/36) + 3*sin(2137*pi/36) - 4*sin(2137*pi/36)**3 + 4*cos(pi/36)**3)*(-3*cos(pi/36) + 4*sin(2137*pi/36)**3 - 3*sin(2137*pi/36) + 4*cos(pi/36)**3),
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
have : (-((-4) * sin(2137 * pi / 36) ** 3 + 3 * sin(2137 * pi / 36)) + cos(pi / 12)) * ((-4) * sin(2137 * pi / 36) ** 3 + 3 * sin(2137 * pi / 36) + cos(pi / 12)) = (3*sin(2137*pi/36) + cos(pi/12) - 4*sin(2137*pi/36)**3)*(4*sin(2137*pi/36)**3 + cos(pi/12) - 3*sin(2137*pi/36)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2137*pi/12) = -4 * sin(2137*pi/36) ** 3 + 3 * sin(2137*pi/36),
{
have : sin(2137*pi/12) = sin(3*(2137*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(2137*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi/12) + cos(pi/12))*(sin(pi/12) + cos(pi/12)) = -sin(pi/12)**2 + cos(pi/12)**2,
{
ring_exp,
},
rw this,
have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
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
rw this,
rw cos_pi_div_six,
end


lemma Trigo_1_94_OCTT_extend : -cos(941*pi/12)**2 - sin(pi/12)**2 + 1=sqrt(3)/2:=
begin
have : -sin(pi / 12) ** 2 - (2 * cos(941 * pi / 12) ** 2 - 1) / 2 + 1 / 2 = -cos(941*pi/12)**2 - sin(pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(941*pi/6) = 2 * cos(941*pi/12) ** 2 - 1,
{
have : cos(941*pi/6) = cos(2*(941*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) ** 2 + (1 / 2 - cos(941 * pi / 6) / 2) = -sin(pi/12)**2 - cos(941*pi/6)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(941*pi/12) ** 2 = 1 / 2 - cos(941*pi/6) / 2,
{
have : cos(941*pi/6) = cos(2*(941*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(941*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
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
rw this,
rw cos_pi_div_six,
end


lemma Trigo_1_95_OVAE_extend (h0 : cos(25*pi/6)≠ 0) (h1 : (4*cos(25*pi/6)**2)≠ 0) (h2 : (2*cos(25*pi/6))≠ 0) (h3 : (4*(cos(-pi/3)*cos(9*pi/2)-sin(-pi/3)*sin(9*pi/2))**2)≠ 0) (h4 : (4*(-sin(9*pi/2)*sin(-pi/3)+cos(9*pi/2)*cos(-pi/3))**2)≠ 0) (h5 : (4*(-cos(9*pi/2)*cos(548*pi/3)-sin(-pi/3)*sin(9*pi/2))**2)≠ 0) (h6 : (4*(-cos(548*pi/3)*cos(9*pi/2)-sin(-pi/3)*sin(9*pi/2))**2)≠ 0) : -sqrt(3)*sin(25*pi/3)**2/(4*(-cos(9*pi/2)*cos(548*pi/3) - sin(-pi/3)*sin(9*pi/2))**2) + sin(25*pi/3)/2=0:=
begin
have : -sqrt 3 * sin(25 * pi / 3) ** 2 / (4 * (-cos(548 * pi / 3) * cos(9 * pi / 2) - sin(-pi / 3) * sin(9 * pi / 2)) ** 2) + sin(25 * pi / 3) / 2 = -sqrt(3)*sin(25*pi/3)**2/(4*(-cos(9*pi/2)*cos(548*pi/3) - sin(-pi/3)*sin(9*pi/2))**2) + sin(25*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -cos(548*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-pi/3) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * sin(25 * pi / 3) ** 2 / (4 * (-sin(9 * pi / 2) * sin(-pi / 3) + cos(9 * pi / 2) * cos(-pi / 3)) ** 2) + sin(25 * pi / 3) / 2 = -sqrt(3)*sin(25*pi/3)**2/(4*(cos(-pi/3)*cos(9*pi/2) - sin(-pi/3)*sin(9*pi/2))**2) + sin(25*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/6) = -sin(9*pi/2) * sin(-pi/3) + cos(9*pi/2) * cos(-pi/3),
{
have : cos(25*pi/6) = cos((9*pi/2) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * (sin(25 * pi / 3) / (2 * cos(25 * pi / 6))) ** 2 + sin(25 * pi / 3) / (2 * cos(25 * pi / 6)) * cos(25 * pi / 6) = -sqrt(3)*sin(25*pi/3)**2/(4*cos(25*pi/6)**2) + sin(25*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/6) = sin(25*pi/3) / ( 2 * cos(25*pi/6) ),
{
have : sin(25*pi/3) = sin(2*(25*pi/6)),
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
have : sin(25*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(25*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_96_YBNQ_extend (h0 : cos(5*pi/12)≠ 0) (h1 : (2*cos(5*pi/12))≠ 0) (h2 : (16*cos(5*pi/12)**4)≠ 0) : -sin(5*pi/6)**4/(16*cos(5*pi/12)**4) + ((-1 + 2*cos(3*pi/8)**2)*cos(-pi/3) - sin(-pi/3)*sin(3*pi/4))**4=-sqrt(3)/2:=
begin
have : -(sin(5 * pi / 6) / (2 * cos(5 * pi / 12))) ** 4 + ((-1 + 2 * cos(3 * pi / 8) ** 2) * cos(-pi / 3) - sin(-pi / 3) * sin(3 * pi / 4)) ** 4 = -sin(5*pi/6)**4/(16*cos(5*pi/12)**4) + ((-1 + 2*cos(3*pi/8)**2)*cos(-pi/3) - sin(-pi/3)*sin(3*pi/4))**4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = sin(5*pi/6) / ( 2 * cos(5*pi/12) ),
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
have : -sin(5 * pi / 12) ** 4 + (cos(-pi / 3) * (2 * cos(3 * pi / 8) ** 2 - 1) - sin(-pi / 3) * sin(3 * pi / 4)) ** 4 = -sin(5*pi/12)**4 + ((-1 + 2*cos(3*pi/8)**2)*cos(-pi/3) - sin(-pi/3)*sin(3*pi/4))**4,
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
have : -sin(5 * pi / 12) ** 4 + (-sin(3 * pi / 4) * sin(-pi / 3) + cos(3 * pi / 4) * cos(-pi / 3)) ** 4 = -sin(5*pi/12)**4 + (cos(-pi/3)*cos(3*pi/4) - sin(-pi/3)*sin(3*pi/4))**4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = -sin(3*pi/4) * sin(-pi/3) + cos(3*pi/4) * cos(-pi/3),
{
have : cos(5*pi/12) = cos((3*pi/4) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5*pi/12)**4 + cos(5*pi/12)**4 = (-sin(5*pi/12)**2 + cos(5*pi/12)**2)*(cos(5*pi/12)**2 + sin(5*pi/12)**2),
{
ring_exp,
},
rw this,
have : cos(5*pi/12)**2 + sin(5*pi/12)**2 = 1,
{
rw add_comm,
rw sin_sq_add_cos_sq,
},
rw this,
have : -sin(5*pi/12)**2 + cos(5*pi/12)**2 = cos(5*pi/6),
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
rw this,
have : cos(5*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -cos(pi/6) = -sqrt(3)/2,
{
have : cos(pi/6) = sqrt(3)/2,
{
rw cos_pi_div_six,
},
linarith,
},
rw this,
norm_num,
end


lemma Trigo_1_97_TAKY_extend : 2*sin(161*pi)*cos(27*pi/2) + 1 - 2*sin(pi/2)*cos(161*pi)=3:=
begin
have : cos(pi/2) = cos(27*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 + 2 * (sin(161 * pi) * cos(pi / 2) - sin(pi / 2) * cos(161 * pi)) = 2*sin(161*pi)*cos(pi/2) + 1 - 2*sin(pi/2)*cos(161*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(321*pi/2) = sin(161*pi) * cos(pi/2) - sin(pi/2) * cos(161*pi),
{
have : sin(321*pi/2) = sin((161*pi) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(321 * pi / 2) + 1 = 1 + 2*sin(321*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = sin(321*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/2) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_pi_div_two,
norm_num,
end


lemma Trigo_1_98_NLRE_extend : -sin(1697*pi/12)*sin(3491*pi/12)=1/4:=
begin
have : sin(1763*pi/12) = sin(3491*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (1763*pi/12) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(1763 * pi / 12) * sin(1697 * pi / 12) = -sin(1697*pi/12)*sin(1763*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(1763*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * -sin(1697 * pi / 12) = -sin(pi/12)*sin(1697*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = -sin(1697*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/12) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*sin(5*pi/12) = -cos(pi/2)/2 + cos(pi/3)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((5*pi/12) + (pi/12)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/12) - (pi/12)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw cos_pi_div_two,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_1_99_BFEN_extend : (-2*sin(691*pi/6)*cos(5*pi/12) - 2*sin(-pi/3)*sin(5*pi/12))*cos(1051*pi/12)=1/2:=
begin
have : 2 * (-sin(691 * pi / 6) * cos(5 * pi / 12) - sin(-pi / 3) * sin(5 * pi / 12)) * cos(1051 * pi / 12) = (-2*sin(691*pi/6)*cos(5*pi/12) - 2*sin(-pi/3)*sin(5*pi/12))*cos(1051*pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/3) = -sin(691*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/3) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (-sin(5 * pi / 12) * sin(-pi / 3) + cos(5 * pi / 12) * cos(-pi / 3)) * cos(1051 * pi / 12) = 2*(cos(-pi/3)*cos(5*pi/12) - sin(-pi/3)*sin(5*pi/12))*cos(1051*pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -sin(5*pi/12) * sin(-pi/3) + cos(5*pi/12) * cos(-pi/3),
{
have : cos(pi/12) = cos((5*pi/12) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(1051 * pi / 12) * cos(pi / 12) = 2*cos(pi/12)*cos(1051*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/12) = cos(1051*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/12) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/12) = sin(pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 2*sin(pi/12)*cos(pi/12) = sin(pi/6),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_2_100_EZFL_extend : -sqrt(3)*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3))**2 - (sin(pi)*sin(31*pi/6) + (cos(pi)*cos(37*pi/6) + sin(pi)*sin(37*pi/6))*cos(pi))*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3))=-sqrt(3)/2:=
begin
have : -sqrt 3 * (sin(14 * pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(14 * pi / 3)) ** 2 - (sin(pi) * sin(31 * pi / 6) + cos(pi) * (sin(37 * pi / 6) * sin(pi) + cos(37 * pi / 6) * cos(pi))) * (sin(14 * pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(14 * pi / 3)) = -sqrt(3)*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3))**2 - (sin(pi)*sin(31*pi/6) + (cos(pi)*cos(37*pi/6) + sin(pi)*sin(37*pi/6))*cos(pi))*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(31*pi/6) = sin(37*pi/6) * sin(pi) + cos(37*pi/6) * cos(pi),
{
have : cos(31*pi/6) = cos((37*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * (sin(14 * pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(14 * pi / 3)) ** 2 - (sin(14 * pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(14 * pi / 3)) * (sin(31 * pi / 6) * sin(pi) + cos(31 * pi / 6) * cos(pi)) = -sqrt(3)*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3))**2 - (sin(pi)*sin(31*pi/6) + cos(pi)*cos(31*pi/6))*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/6) = sin(31*pi/6) * sin(pi) + cos(31*pi/6) * cos(pi),
{
have : cos(25*pi/6) = cos((31*pi/6) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * (sin(14 * pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(14 * pi / 3)) ** 2 - (sin(14 * pi / 3) * cos(pi / 2) - sin(pi / 2) * cos(14 * pi / 3)) * cos(25 * pi / 6) = -sqrt(3)*(sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3))**2 - (sin(14*pi/3)*cos(pi/2) - sin(pi/2)*cos(14*pi/3))*cos(25*pi/6),
{
field_simp at *,
},
have : sin(25*pi/6) = sin(14*pi/3) * cos(pi/2) - sin(pi/2) * cos(14*pi/3),
{
have : sin(25*pi/6) = sin((14*pi/3) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(25*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_101_VKRO_extend (h0 : cos(733*pi/12)≠ 0) (h1 : (2*cos(733*pi/12))≠ 0) : -sin(1369*pi/12)*sin(733*pi/6)/(2*cos(733*pi/12)) + sin(7*pi/12)*cos(pi/12)=1:=
begin
have : -(sin(733 * pi / 6) / (2 * cos(733 * pi / 12))) * sin(1369 * pi / 12) + sin(7 * pi / 12) * cos(pi / 12) = -sin(1369*pi/12)*sin(733*pi/6)/(2*cos(733*pi/12)) + sin(7*pi/12)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(733*pi/12) = sin(733*pi/6) / ( 2 * cos(733*pi/12) ),
{
have : sin(733*pi/6) = sin(2*(733*pi/12)),
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
have : cos(5*pi/12) = sin(1369*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(733*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/12) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*cos(5*pi/12) = -sin(pi/3)/2 + sin(pi/2)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((5*pi/12) + (pi/12)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((5*pi/12) - (pi/12)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(7*pi/12)*cos(pi/12) = sin(2*pi/3)/2 + sin(pi/2)/2,
{
rw sin_mul_cos,
have : sin((7*pi/12) + (pi/12)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((7*pi/12) - (pi/12)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_two,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_102_XATR_extend (h0 : cos(pi/12)≠ 0) (h1 : (4*cos(pi/12)**2)≠ 0) (h2 : (2*cos(pi/12))≠ 0) : -sin(1585*pi/12)**2 - sin(pi/6)**2/(4*cos(pi/12)**2) + 1=sqrt(3)/2:=
begin
have : -(sin(pi / 6) / (2 * cos(pi / 12))) ** 2 - sin(1585 * pi / 12) ** 2 + 1 = -sin(1585*pi/12)**2 - sin(pi/6)**2/(4*cos(pi/12)**2) + 1,
{
field_simp at *,
ring,
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
have : -(-sin(1585 * pi / 12)) ** 2 - sin(pi / 12) ** 2 + 1 = -sin(pi/12)**2 - sin(1585*pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/12) = -sin(1585*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/12) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) ** 2 + (1 - sin(-pi / 12) ** 2) = -sin(-pi/12)**2 - sin(pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/12) ** 2 = 1 - sin(-pi/12) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : cos(-pi/12) = cos(pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
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
rw this,
rw cos_pi_div_six,
end


lemma Trigo_2_103_PTKE_extend : -sin(pi/4)**2 + cos(947*pi/4)**2 - 2*sin(pi/4)*cos(947*pi/4)=1:=
begin
have : sin(197*pi/4) = cos(947*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (197*pi/4) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 4) ** 2 + (-sin(197 * pi / 4)) ** 2 + 2 * sin(pi / 4) * -sin(197 * pi / 4) = -sin(pi/4)**2 + sin(197*pi/4)**2 - 2*sin(pi/4)*sin(197*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/4) = -sin(197*pi/4),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(pi / 4) * cos(pi / 4) + (-sin(pi / 4) ** 2 + cos(pi / 4) ** 2) = -sin(pi/4)**2 + cos(pi/4)**2 + 2*sin(pi/4)*cos(pi/4),
{
field_simp at *,
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
have : 2*sin(pi/4)*cos(pi/4) = sin(pi/2),
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
rw cos_pi_div_two,
rw sin_pi_div_two,
norm_num,
end


lemma Trigo_2_104_GLWU_extend : -sin(889*pi/12)*cos(1147*pi/12) - cos(pi/12)*cos(637*pi/12)=sqrt(3)/2:=
begin
have : cos(5*pi/12) = cos(1147*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/12) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(889*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) * cos(5 * pi / 12) + -cos(637 * pi / 12) * cos(pi / 12) = -sin(pi/12)*cos(5*pi/12) - cos(pi/12)*cos(637*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = -cos(637*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/12) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12) = sin(pi/3),
{
have : sin(pi/3) = sin((5*pi/12) - (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_2_105_DEZF_extend : -4*(-4*sin(25*pi/36)**3 + 3*sin(25*pi/36))**2*sin(1805*pi/12)**2 + 1=3/4:=
begin
have : (-4) * ((-4) * sin(25 * pi / 36) ** 3 + 3 * sin(25 * pi / 36)) ** 2 * sin(1805 * pi / 12) ** 2 + 1 = -4*(-4*sin(25*pi/36)**3 + 3*sin(25*pi/36))**2*sin(1805*pi/12)**2 + 1,
{
field_simp at *,
},
have : sin(25*pi/12) = -4 * sin(25*pi/36) ** 3 + 3 * sin(25*pi/36),
{
have : sin(25*pi/12) = sin(3*(25*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-4) * sin(25 * pi / 12) ** 2 * sin(1805 * pi / 12) ** 2 + 1 = -4*sin(25*pi/12)**2*sin(1805*pi/12)**2 + 1,
{
field_simp at *,
},
have : cos(25*pi/12) = sin(1805*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (25*pi/12) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - (2 * sin(25 * pi / 12) * cos(25 * pi / 12)) ** 2 = -4*sin(25*pi/12)**2*cos(25*pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/6) = 2 * sin(25*pi/12) * cos(25*pi/12),
{
have : sin(25*pi/6) = sin(2*(25*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_2_106_JRSX_extend : (2*sin(227*pi/4)*cos(pi/3) - (2*sin(0)*cos(-pi/3) - 2*sin(-pi/3)*cos(0))*cos(3*pi/4))*cos(5*pi/12)=1/2:=
begin
have : (2 * sin(227 * pi / 4) * cos(pi / 3) - 2 * (sin(0) * cos(-pi / 3) - sin(-pi / 3) * cos(0)) * cos(3 * pi / 4)) * cos(5 * pi / 12) = (2*sin(227*pi/4)*cos(pi/3) - (2*sin(0)*cos(-pi/3) - 2*sin(-pi/3)*cos(0))*cos(3*pi/4))*cos(5*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/4) = sin(227*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (3*pi/4) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sin(3 * pi / 4) * cos(pi / 3) - (sin(0) * cos(-pi / 3) - sin(-pi / 3) * cos(0)) * cos(3 * pi / 4)) * cos(5 * pi / 12) = (2*sin(3*pi/4)*cos(pi/3) - 2*(sin(0)*cos(-pi/3) - sin(-pi/3)*cos(0))*cos(3*pi/4))*cos(5*pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = sin(0) * cos(-pi/3) - sin(-pi/3) * cos(0),
{
have : sin(pi/3) = sin((0) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = sin(3*pi/4) * cos(pi/3) - sin(pi/3) * cos(3*pi/4),
{
have : sin(5*pi/12) = sin((3*pi/4) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*sin(5*pi/12)*cos(5*pi/12) = sin(5*pi/6),
{
have : sin(5*pi/6) = sin(2*(5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_2_107_FWSU_extend : cos(43*pi/180)*cos(23473*pi/180) + sin(35713*pi/180)*cos(23087*pi/180)=sqrt(3)/2:=
begin
have : cos(17*pi/180) = sin(35713*pi/180),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (17*pi/180) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(43 * pi / 180) * cos(23473 * pi / 180) + cos(23087 * pi / 180) * cos(17 * pi / 180) = cos(43*pi/180)*cos(23473*pi/180) + cos(17*pi/180)*cos(23087*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi/180) = cos(23087*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (43*pi/180) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(23473 * pi / 180) * cos(43 * pi / 180) + sin(43 * pi / 180) * cos(17 * pi / 180) = cos(43*pi/180)*cos(23473*pi/180) + sin(43*pi/180)*cos(17*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/180) = cos(23473*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (17*pi/180) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(17*pi/180) = sin(pi/3),
{
have : sin(pi/3) = sin((17*pi/180) + (43*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_2_108_CKZV_extend : sin(-2*pi)*cos(-19*pi/6) + cos(235*pi/3)/2 - sin(7*pi/6)/2=1/2:=
begin
have : sin((-2) * pi) * cos((-19) * pi / 6) + cos(235 * pi / 3) / 2 - sin(7 * pi / 6) / 2 = sin(-2*pi)*cos(-19*pi/6) + cos(235*pi/3)/2 - sin(7*pi/6)/2,
{
field_simp at *,
},
have : sin(-31*pi/6) = cos(235*pi/3),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-31*pi/6) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * pi) * cos((-19) * pi / 6) + (-sin(7 * pi / 6) / 2 + sin((-31) * pi / 6) / 2) = sin(-2*pi)*cos(-19*pi/6) + sin(-31*pi/6)/2 - sin(7*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-19*pi/6) * cos(-2*pi) = -sin(7*pi/6) / 2 + sin(-31*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-2*pi) + (-19*pi/6)) = sin(-31*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-2*pi) - (-19*pi/6)) = sin(7*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-19*pi/6) * cos(-2*pi)) = sin(-19*pi/6)*cos(-2*pi),
{
ring,
},
have : sin((-19) * pi / 6) * cos((-2) * pi) + sin((-2) * pi) * cos((-19) * pi / 6) = sin(-2*pi)*cos(-19*pi/6) + sin(-19*pi/6)*cos(-2*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-31*pi/6) = sin(-19*pi/6) * cos(-2*pi) + sin(-2*pi) * cos(-19*pi/6),
{
have : sin(-31*pi/6) = sin((-19*pi/6) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-31*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-31*pi/6) (-3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_2_109_GAYY_extend : (1 - 2*sin(pi/16)**2)*(-4*(-4*sin(pi/72)**3 + 3*sin(pi/72))**3 - 12*sin(pi/72)**3 + 9*sin(pi/72))=sqrt(2)/4:=
begin
have : (1 - 2 * sin(pi / 16) ** 2) * ((-4) * ((-4) * sin(pi / 72) ** 3 + 3 * sin(pi / 72)) ** 3 + 3 * ((-4) * sin(pi / 72) ** 3 + 3 * sin(pi / 72))) = (1 - 2*sin(pi/16)**2)*(-4*(-4*sin(pi/72)**3 + 3*sin(pi/72))**3 - 12*sin(pi/72)**3 + 9*sin(pi/72)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/24) = -4 * sin(pi/72) ** 3 + 3 * sin(pi/72),
{
have : sin(pi/24) = sin(3*(pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(pi / 24) ** 3 + 3 * sin(pi / 24)) * (1 - 2 * sin(pi / 16) ** 2) = (1 - 2*sin(pi/16)**2)*(-4*sin(pi/24)**3 + 3*sin(pi/24)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : ((-4) * sin(pi / 24) ** 3 + 3 * sin(pi / 24)) * cos(pi / 8) = (-4*sin(pi/24)**3 + 3*sin(pi/24))*cos(pi/8),
{
field_simp at *,
},
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
have : sin(pi/8)*cos(pi/8) = sin(pi/4)/2,
{
have : sin(pi/4) = 2*sin(pi/8)*cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_2_110_VRLM_extend (h0 : (sin((-35)*pi/6)**2-cos((-16)*pi/3)-cos((-29)*pi/6)**2+1)≠ 0) (h1 : (-cos(-29*pi/6)**2+sin(-35*pi/6)**2-cos(-16*pi/3)+1)≠ 0) (h2 : (-cos(-29*pi/6)**2+sin(-35*pi/6)**2+cos(503*pi/3)+1)≠ 0) (h3 : (-cos((-29)*pi/6)**2+sin((-35)*pi/6)**2- -cos(503*pi/3)+1)≠ 0) (h4 : (-cos((-29)*pi/6)**2+(1/2-cos((-35)*pi/3)/2)+cos(503*pi/3)+1)≠ 0) (h5 : (-cos(-29*pi/6)**2-cos(-35*pi/3)/2+cos(503*pi/3)+3/2)≠ 0) : (-sin(-13*pi/3) + 2*sin(943*pi/6)*cos(41*pi/6))/(-cos(-29*pi/6)**2 - cos(-35*pi/3)/2 + cos(503*pi/3) + 3/2)=sqrt(3):=
begin
have : (-sin((-13) * pi / 3) + 2 * sin(943 * pi / 6) * cos(41 * pi / 6)) / (-cos((-29) * pi / 6) ** 2 + (1 / 2 - cos((-35) * pi / 3) / 2) + cos(503 * pi / 3) + 1) = (-sin(-13*pi/3) + 2*sin(943*pi/6)*cos(41*pi/6))/(-cos(-29*pi/6)**2 - cos(-35*pi/3)/2 + cos(503*pi/3) + 3/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-35*pi/6) ** 2 = 1 / 2 - cos(-35*pi/3) / 2,
{
have : cos(-35*pi/3) = cos(2*(-35*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin((-13) * pi / 3) + 2 * sin(943 * pi / 6) * cos(41 * pi / 6)) / (-cos((-29) * pi / 6) ** 2 + sin((-35) * pi / 6) ** 2 - -cos(503 * pi / 3) + 1) = (-sin(-13*pi/3) + 2*sin(943*pi/6)*cos(41*pi/6))/(-cos(-29*pi/6)**2 + sin(-35*pi/6)**2 + cos(503*pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-16*pi/3) = -cos(503*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-16*pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * sin(943 * pi / 6) * cos(41 * pi / 6) - sin((-13) * pi / 3)) / (sin((-35) * pi / 6) ** 2 - cos((-16) * pi / 3) - cos((-29) * pi / 6) ** 2 + 1) = (-sin(-13*pi/3) + 2*sin(943*pi/6)*cos(41*pi/6))/(-cos(-29*pi/6)**2 + sin(-35*pi/6)**2 - cos(-16*pi/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-29*pi/6) = sin(943*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-29*pi/6) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-13*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-13*pi/3) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-29*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(41*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (41*pi/6) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-29*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-35*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-35*pi/6) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-16*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-16*pi/3) (-3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
rw sin_pi_div_three,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_2_111_AOAD_extend : sin(-5363*pi/30)/2 - sin(1079*pi/6)/2 + (-4*sin(pi/15)**3 + 3*sin(pi/15))*sin(7*pi/15)=1/2:=
begin
have : -(-sin((-5363) * pi / 30) / 2 + sin(1079 * pi / 6) / 2) + ((-4) * sin(pi / 15) ** 3 + 3 * sin(pi / 15)) * sin(7 * pi / 15) = sin(-5363*pi/30)/2 - sin(1079*pi/6)/2 + (-4*sin(pi/15)**3 + 3*sin(pi/15))*sin(7*pi/15),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1793*pi/10) * cos(8*pi/15) = -sin(-5363*pi/30) / 2 + sin(1079*pi/6) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((8*pi/15) + (1793*pi/10)) = sin(1079*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((8*pi/15) - (1793*pi/10)) = sin(-5363*pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(1793*pi/10) * cos(8*pi/15)) = -sin(1793*pi/10)*cos(8*pi/15),
{
ring,
},
conv {to_lhs, rw this,},
have : -sin(1793 * pi / 10) * cos(8 * pi / 15) + ((-4) * sin(pi / 15) ** 3 + 3 * sin(pi / 15)) * sin(7 * pi / 15) = -sin(1793*pi/10)*cos(8*pi/15) + (-4*sin(pi/15)**3 + 3*sin(pi/15))*sin(7*pi/15),
{
field_simp at *,
},
have : cos(pi/5) = -sin(1793*pi/10),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/5) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(pi / 15) ** 3 + 3 * sin(pi / 15)) * sin(7 * pi / 15) + cos(pi / 5) * cos(8 * pi / 15) = cos(pi/5)*cos(8*pi/15) + (-4*sin(pi/15)**3 + 3*sin(pi/15))*sin(7*pi/15),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi/5)*cos(8*pi/15) = cos(11*pi/15)/2 + cos(pi/3)/2,
{
rw mul_comm,
rw cos_mul_cos,
have : cos((8*pi/15) + (pi/5)) = cos(11*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : cos((8*pi/15) - (pi/5)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(pi/5)*sin(7*pi/15) = -cos(2*pi/3)/2 + cos(4*pi/15)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((7*pi/15) + (pi/5)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((7*pi/15) - (pi/5)) = cos(4*pi/15),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(11*pi/15) = -cos(4*pi/15),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (11*pi/15) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_112_CUYK_extend (h0 : tan(377*pi/4)≠ 0) : -sin(5*pi/2) + sin(4*pi/3) - sin(190*pi/3) + 1/tan(377*pi/4)=0:=
begin
have : -sin(5 * pi / 2) + sin(4 * pi / 3) - sin(190 * pi / 3) - (-1) / tan(377 * pi / 4) = -sin(5*pi/2) + sin(4*pi/3) - sin(190*pi/3) + 1/tan(377*pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(367*pi/4) = -1 / tan(377*pi/4),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (367*pi/4) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(5 * pi / 2) + sin(4 * pi / 3) - sin(190 * pi / 3) + -tan(367 * pi / 4) = -sin(5*pi/2) + sin(4*pi/3) - sin(190*pi/3) - tan(367*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(9*pi/4) = -tan(367*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (9*pi/4) (94),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 3) - sin(5 * pi / 2) + -sin(190 * pi / 3) + tan(9 * pi / 4) = -sin(5*pi/2) + sin(4*pi/3) - sin(190*pi/3) + tan(9*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/6) = -sin(190*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (25*pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/2) = sin(pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (5*pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(4*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(25*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(9*pi/4) = tan(pi/4),
{
rw tan_eq_tan_add_int_mul_pi (9*pi/4) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_two,
rw sin_pi_div_three,
rw cos_pi_div_six,
rw tan_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_2_113_GCGI_extend : cos(2561*pi/6)/2=-sqrt(3)/4:=
begin
have : cos(1733*pi/6) = cos(2561*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (1733*pi/6) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 - (1 / 2 - cos(1733 * pi / 6) / 2) = cos(1733*pi/6)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1733*pi/12) ** 2 = 1 / 2 - cos(1733*pi/6) / 2,
{
have : cos(1733*pi/6) = cos(2*(1733*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = sin(1733*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12)**2 = cos(pi/6)/2 + 1/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
rw cos_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_2_114_VFFU_extend : -sin(5*pi/12)/2 + sin(pi/4)/2 + (sin(-2*pi)*sin(395*pi/6) + cos(-2*pi)*cos(395*pi/6))*sin(5*pi/12)=sqrt(2)/2:=
begin
have : -sin(5 * pi / 12) / 2 + sin(pi / 4) / 2 + sin(5 * pi / 12) * (sin(395 * pi / 6) * sin((-2) * pi) + cos(395 * pi / 6) * cos((-2) * pi)) = -sin(5*pi/12)/2 + sin(pi/4)/2 + (sin(-2*pi)*sin(395*pi/6) + cos(-2*pi)*cos(395*pi/6))*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(407*pi/6) = sin(395*pi/6) * sin(-2*pi) + cos(395*pi/6) * cos(-2*pi),
{
have : cos(407*pi/6) = cos((395*pi/6) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = cos(407*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(-sin(pi / 4) / 2 + sin(5 * pi / 12) / 2) + sin(5 * pi / 12) * cos(pi / 6) = -sin(5*pi/12)/2 + sin(pi/4)/2 + sin(5*pi/12)*cos(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) * cos(pi/3) = -sin(pi/4) / 2 + sin(5*pi/12) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((pi/3) + (pi/12)) = sin(5*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/3) - (pi/12)) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(pi/12) * cos(pi/3)) = -sin(pi/12)*cos(pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/3) = sin(pi/6),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(pi/12)*sin(pi/6) + cos(pi/12)*cos(pi/6) = cos(pi/4),
{
have : cos(pi/4) = cos((pi/6) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_2_115_FOXM_extend : (sin(-5*pi/18)*sin(pi/2) - cos(pi/2)*cos(977*pi/18))*sin(557*pi/9) + sin(2*pi/9)*cos(pi/9)=sqrt(3)/2:=
begin
have : -(cos(977 * pi / 18) * cos(pi / 2) - sin((-5) * pi / 18) * sin(pi / 2)) * sin(557 * pi / 9) + sin(2 * pi / 9) * cos(pi / 9) = (sin(-5*pi/18)*sin(pi/2) - cos(pi/2)*cos(977*pi/18))*sin(557*pi/9) + sin(2*pi/9)*cos(pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-5*pi/18) = cos(977*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-5*pi/18) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(557 * pi / 9) * (-sin((-5) * pi / 18) * sin(pi / 2) + cos((-5) * pi / 18) * cos(pi / 2)) + sin(2 * pi / 9) * cos(pi / 9) = -(cos(-5*pi/18)*cos(pi/2) - sin(-5*pi/18)*sin(pi/2))*sin(557*pi/9) + sin(2*pi/9)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = -sin(-5*pi/18) * sin(pi/2) + cos(-5*pi/18) * cos(pi/2),
{
have : cos(2*pi/9) = cos((-5*pi/18) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = -sin(557*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/9) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9)*cos(2*pi/9) + sin(2*pi/9)*cos(pi/9) = sin(pi/3),
{
have : sin(pi/3) = sin((pi/9) + (2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_2_116_GRUD_extend (h0 : cos(pi/12)≠ 0) (h1 : (2*cos(pi/12))≠ 0) (h2 : cos(pi/6)≠ 0) (h3 : (4*cos(pi/12)*cos(pi/6))≠ 0) (h4 : (2*cos(pi/6))≠ 0) : (-sin(pi/6)/(2*cos(pi/12)) + cos(pi/12))*(sin(pi/6)/(2*cos(pi/12)) + cos(pi/12))=sqrt(3)/2:=
begin
have : (-(2 * sin(pi / 6) * cos(pi / 6)) / (4 * cos(pi / 12) * cos(pi / 6)) + cos(pi / 12)) * (2 * sin(pi / 6) * cos(pi / 6) / (4 * cos(pi / 12) * cos(pi / 6)) + cos(pi / 12)) = (-sin(pi/6)/(2*cos(pi/12)) + cos(pi/12))*(sin(pi/6)/(2*cos(pi/12)) + cos(pi/12)),
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
have : (-(sin(pi / 3) / (2 * cos(pi / 6))) / (2 * cos(pi / 12)) + cos(pi / 12)) * (sin(pi / 3) / (2 * cos(pi / 6)) / (2 * cos(pi / 12)) + cos(pi / 12)) = (-sin(pi/3)/(4*cos(pi/12)*cos(pi/6)) + cos(pi/12))*(sin(pi/3)/(4*cos(pi/12)*cos(pi/6)) + cos(pi/12)),
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
have : (-(sin(pi / 6) / (2 * cos(pi / 12))) + cos(pi / 12)) * (sin(pi / 6) / (2 * cos(pi / 12)) + cos(pi / 12)) = (-sin(pi/6)/(2*cos(pi/12)) + cos(pi/12))*(sin(pi/6)/(2*cos(pi/12)) + cos(pi/12)),
{
field_simp at *,
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
have : (-sin(pi/12) + cos(pi/12))*(sin(pi/12) + cos(pi/12)) = -sin(pi/12)**2 + cos(pi/12)**2,
{
ring_exp,
},
rw this,
have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
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
rw this,
rw cos_pi_div_six,
end


lemma Trigo_2_117_ZIKP_extend : sin(-pi/3)/2 + sin(pi/2)/2 + sin(7*pi/12)*cos(-1441*pi/12)=1:=
begin
have : sin(-pi / 3) / 2 + sin(pi / 2) / 2 + sin(7 * pi / 12) * cos((-1441) * pi / 12) = sin(-pi/3)/2 + sin(pi/2)/2 + sin(7*pi/12)*cos(-1441*pi/12),
{
field_simp at *,
},
have : sin(pi/12) * cos(5*pi/12) = sin(-pi/3) / 2 + sin(pi/2) / 2,
{
rw sin_mul_cos,
have : sin((pi/12) + (5*pi/12)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/12) - (5*pi/12)) = sin(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/12) * cos(5*pi/12)) = sin(pi/12)*cos(5*pi/12),
{
ring,
},
have : sin(pi / 12) * cos(5 * pi / 12) + sin(7 * pi / 12) * cos((-1441) * pi / 12) = sin(pi/12)*cos(5*pi/12) + sin(7*pi/12)*cos(-1441*pi/12),
{
field_simp at *,
},
have : cos(1537*pi/12) = cos(-1441*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (1537*pi/12) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = cos(1537*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/12) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) = sin(5*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12) = sin(pi/2),
{
have : sin(pi/2) = sin((pi/12) + (5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_two,
end


lemma Trigo_2_118_YDUQ_extend (h0 : (-sin(-29*pi/6)**2+sin(-35*pi/6)**2+sin(41*pi/6)+2)≠ 0) (h1 : (sin((-35)*pi/6)**2+sin(41*pi/6)+(1-sin((-29)*pi/6)**2)+1)≠ 0) (h2 : (-sin(-29*pi/6)**2+sin(-35*pi/6)**2+2*sin(41*pi/12)*cos(41*pi/12)+2)≠ 0) (h3 : (-sin((-29)*pi/6)**2+sin((-35)*pi/6)**2+2*sin(41*pi/12)*cos(41*pi/12)+2)≠ 0) (h4 : (-sin(-29*pi/6)**2+sin(-35*pi/6)**2+2*(-1+2*cos(41*pi/24)**2)*sin(41*pi/12)+2)≠ 0) (h5 : (-sin((-29)*pi/6)**2+sin((-35)*pi/6)**2+2*sin(41*pi/12)*(2*cos(41*pi/24)**2-1)+2)≠ 0) : (sin(-29*pi/6)*cos(41*pi/6) - 2*cos(-29*pi/6))/(-sin(-29*pi/6)**2 + sin(-35*pi/6)**2 + 2*(-1 + 2*cos(41*pi/24)**2)*sin(41*pi/12) + 2)=sqrt(3)/2:=
begin
have : (sin((-29) * pi / 6) * cos(41 * pi / 6) - 2 * cos((-29) * pi / 6)) / (-sin((-29) * pi / 6) ** 2 + sin((-35) * pi / 6) ** 2 + 2 * sin(41 * pi / 12) * (2 * cos(41 * pi / 24) ** 2 - 1) + 2) = (sin(-29*pi/6)*cos(41*pi/6) - 2*cos(-29*pi/6))/(-sin(-29*pi/6)**2 + sin(-35*pi/6)**2 + 2*(-1 + 2*cos(41*pi/24)**2)*sin(41*pi/12) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(41*pi/12) = 2 * cos(41*pi/24) ** 2 - 1,
{
have : cos(41*pi/12) = cos(2*(41*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : (sin((-29) * pi / 6) * cos(41 * pi / 6) - 2 * cos((-29) * pi / 6)) / (-sin((-29) * pi / 6) ** 2 + sin((-35) * pi / 6) ** 2 + 2 * sin(41 * pi / 12) * cos(41 * pi / 12) + 2) = (sin(-29*pi/6)*cos(41*pi/6) - 2*cos(-29*pi/6))/(-sin(-29*pi/6)**2 + sin(-35*pi/6)**2 + 2*sin(41*pi/12)*cos(41*pi/12) + 2),
{
field_simp at *,
},
have : sin(41*pi/6) = 2 * sin(41*pi/12) * cos(41*pi/12),
{
have : sin(41*pi/6) = sin(2*(41*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : (sin((-29) * pi / 6) * cos(41 * pi / 6) - 2 * cos((-29) * pi / 6)) / (sin((-35) * pi / 6) ** 2 + sin(41 * pi / 6) + (1 - sin((-29) * pi / 6) ** 2) + 1) = (sin(-29*pi/6)*cos(41*pi/6) - 2*cos(-29*pi/6))/(-sin(-29*pi/6)**2 + sin(-35*pi/6)**2 + sin(41*pi/6) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-29*pi/6) ** 2 = 1 - sin(-29*pi/6) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : sin(-29*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(41*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (41*pi/6) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-29*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-35*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-35*pi/6) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(41*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (41*pi/6) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_119_HTCH_extend : 4*sin(x/3 + 2293*pi/12)**3 - 3*sin(x/3 + 2293*pi/12) - cos(-x + 727*pi/4)=sqrt(2)*sin(x):=
begin
have : -cos(-x + 727 * pi / 4) + 4 * sin(x / 3 + 2293 * pi / 12) ** 3 - 3 * sin(x / 3 + 2293 * pi / 12) = 4*sin(x/3 + 2293*pi/12)**3 - 3*sin(x/3 + 2293*pi/12) - cos(-x + 727*pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/4) = cos(-x + 727*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + pi/4) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(-x + pi / 4) - 4 * (-sin(x / 3 + 2293 * pi / 12)) ** 3 + 3 * -sin(x / 3 + 2293 * pi / 12) = -sin(-x + pi/4) + 4*sin(x/3 + 2293*pi/12)**3 - 3*sin(x/3 + 2293*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/3 + pi/12) = -sin(x/3 + 2293*pi/12),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x/3 + pi/12) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(-x + pi / 4) + ((-4) * sin(x / 3 + pi / 12) ** 3 + 3 * sin(x / 3 + pi / 12)) = -sin(-x + pi/4) - 4*sin(x/3 + pi/12)**3 + 3*sin(x/3 + pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/4) = -4 * sin(x/3 + pi/12) ** 3 + 3 * sin(x/3 + pi/12),
{
have : sin(x + pi/4) = sin(3*(x/3 + pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/4) = -sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(-x+pi/4) = sin((pi/4) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(x + pi/4) = sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(x+pi/4) = sin((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
rw cos_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_120_VMXM_extend (h0 : ((1-1/tan(52*pi/3)**2)*tan(52*pi/3))≠ 0) (h1 : tan(52*pi/3)≠ 0) (h2 : (1-(1/tan(52*pi/3))**2)≠ 0) (h3 : cos((104*pi/3)/2)≠ 0) (h4 : ((1-1/(sin(104*pi/3)/(1+cos(104*pi/3)))**2)*(sin(104*pi/3)/(1+cos(104*pi/3))))≠ 0) (h5 : sin(104*pi/3)≠ 0) (h6 : (sin(104*pi/3)/(1+cos(104*pi/3)))≠ 0) (h7 : ((-(cos(104*pi/3)+1)**2/sin(104*pi/3)**2+1)*sin(104*pi/3))≠ 0) (h8 : (1+cos(104*pi/3))≠ 0) (h9 : ((-(cos(104*pi/3)+1)**2/(2*sin(52*pi/3)*cos(52*pi/3))**2+1)*(2*sin(52*pi/3)*cos(52*pi/3)))≠ 0) (h10 : (2*sin(52*pi/3)*cos(52*pi/3))≠ 0) (h11 : (4*sin(52*pi/3)**2*cos(52*pi/3)**2)≠ 0) (h12 : (2*(-(cos(104*pi/3)+1)**2/(4*sin(52*pi/3)**2*cos(52*pi/3)**2)+1)*sin(52*pi/3)*cos(52*pi/3))≠ 0) : (cos(104*pi/3) + 1)/(2*(-(cos(104*pi/3) + 1)**2/(4*sin(52*pi/3)**2*cos(52*pi/3)**2) + 1)*sin(52*pi/3)*cos(52*pi/3))=sqrt(3)/2:=
begin
have : (cos(104 * pi / 3) + 1) / ((-(cos(104 * pi / 3) + 1) ** 2 / (2 * sin(52 * pi / 3) * cos(52 * pi / 3)) ** 2 + 1) * (2 * sin(52 * pi / 3) * cos(52 * pi / 3))) = (cos(104*pi/3) + 1)/(2*(-(cos(104*pi/3) + 1)**2/(4*sin(52*pi/3)**2*cos(52*pi/3)**2) + 1)*sin(52*pi/3)*cos(52*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(104*pi/3) = 2 * sin(52*pi/3) * cos(52*pi/3),
{
have : sin(104*pi/3) = sin(2*(52*pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : 1 / ((1 - 1 / (sin(104 * pi / 3) / (1 + cos(104 * pi / 3))) ** 2) * (sin(104 * pi / 3) / (1 + cos(104 * pi / 3)))) = (cos(104*pi/3) + 1)/((-(cos(104*pi/3) + 1)**2/sin(104*pi/3)**2 + 1)*sin(104*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(52*pi/3) = sin(104*pi/3) / ( 1 + cos(104*pi/3) ),
{
have : tan(52*pi/3) = tan((104*pi/3)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : 1 / tan(52 * pi / 3) / (1 - (1 / tan(52 * pi / 3)) ** 2) = 1/((1 - 1/tan(52*pi/3)**2)*tan(52*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = 1 / tan(52*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/6) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_pi_div_six,
norm_num,
field_simp,
end


lemma Trigo_2_121_OABC_extend : -((-1 + 2*cos(13*pi/12)**2)*sin(2*pi) + sin(13*pi/6)*cos(2*pi))**2 + ((-1 + 2*cos(13*pi/12)**2)*sin(2*pi) + sin(13*pi/6)*cos(2*pi))*cos(827*pi/6)=sqrt(3)/4-1/4:=
begin
have : cos(25*pi/6) = cos(827*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (25*pi/6) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(2 * pi) * (2 * cos(13 * pi / 12) ** 2 - 1) + sin(13 * pi / 6) * cos(2 * pi)) ** 2 + (sin(2 * pi) * (2 * cos(13 * pi / 12) ** 2 - 1) + sin(13 * pi / 6) * cos(2 * pi)) * cos(25 * pi / 6) = -((-1 + 2*cos(13*pi/12)**2)*sin(2*pi) + sin(13*pi/6)*cos(2*pi))**2 + ((-1 + 2*cos(13*pi/12)**2)*sin(2*pi) + sin(13*pi/6)*cos(2*pi))*cos(25*pi/6),
{
field_simp at *,
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
have : -(sin(13 * pi / 6) * cos(2 * pi) + sin(2 * pi) * cos(13 * pi / 6)) ** 2 + (sin(13 * pi / 6) * cos(2 * pi) + sin(2 * pi) * cos(13 * pi / 6)) * cos(25 * pi / 6) = -(sin(2*pi)*cos(13*pi/6) + sin(13*pi/6)*cos(2*pi))**2 + (sin(2*pi)*cos(13*pi/6) + sin(13*pi/6)*cos(2*pi))*cos(25*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/6) = sin(13*pi/6) * cos(2*pi) + sin(2*pi) * cos(13*pi/6),
{
have : sin(25*pi/6) = sin((13*pi/6) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(25*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/6)**2 = 1/2 - cos(pi/3)/2,
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
have : sin(pi/6)*cos(pi/6) = sin(pi/3)/2,
{
have : sin(pi/3) = 2*sin(pi/6)*cos(pi/6),
{
have : sin(pi/3) = sin(2*(pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_three,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_122_VHED_extend (h0 : (-cos(x+163*pi)+2*cos(-x+11*pi/2))≠ 0) (h1 : (2*cos(-x+11*pi/2)-cos(x+163*pi))≠ 0) (h2 : (-sin(2*pi)*sin(x+165*pi)+2*cos(-x+11*pi/2)-cos(2*pi)*cos(x+165*pi))≠ 0) (h3 : (2*cos(-x+11*pi/2)-(sin(x+165*pi)*sin(2*pi)+cos(x+165*pi)*cos(2*pi)))≠ 0) : (sin(x + pi/2) + 3*cos(x + 159*pi/2))/(-sin(2*pi)*sin(x + 165*pi) + 2*cos(-x + 11*pi/2) - cos(2*pi)*cos(x + 165*pi))=(cos(x)+3*sin(x))/(-2*sin(x)+cos(x)):=
begin
have : (3 * cos(x + 159 * pi / 2) + sin(x + pi / 2)) / (-sin(2 * pi) * sin(x + 165 * pi) + 2 * cos(-x + 11 * pi / 2) - cos(2 * pi) * cos(x + 165 * pi)) = (sin(x + pi/2) + 3*cos(x + 159*pi/2))/(-sin(2*pi)*sin(x + 165*pi) + 2*cos(-x + 11*pi/2) - cos(2*pi)*cos(x + 165*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x - pi) = cos(x + 159*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x - pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (3 * sin(-x - pi) + sin(x + pi / 2)) / (2 * cos(-x + 11 * pi / 2) - (sin(x + 165 * pi) * sin(2 * pi) + cos(x + 165 * pi) * cos(2 * pi))) = (3*sin(-x - pi) + sin(x + pi/2))/(-sin(2*pi)*sin(x + 165*pi) + 2*cos(-x + 11*pi/2) - cos(2*pi)*cos(x + 165*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x + 163*pi) = sin(x + 165*pi) * sin(2*pi) + cos(x + 165*pi) * cos(2*pi),
{
have : cos(x + 163*pi) = cos((x + 165*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (3 * sin(-x - pi) + sin(x + pi / 2)) / (-cos(x + 163 * pi) + 2 * cos(-x + 11 * pi / 2)) = (3*sin(-x - pi) + sin(x + pi/2))/(2*cos(-x + 11*pi/2) - cos(x + 163*pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 5*pi) = cos(x + 163*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 5*pi) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 5*pi) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x + 5*pi) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 11*pi/2) = -sin(x),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 11*pi/2) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
ring_exp,
end


lemma Trigo_2_123_WEDB_extend : (-32*(1 - 2*sin(x/12 + pi/36)**2)**3*sin(x/6 + pi/18)**3 + 6*(1 - 2*sin(x/12 + pi/36)**2)*sin(x/6 + pi/18))**2 + sin(x - pi/6)**2=1:=
begin
have : ((-32) * sin(x / 6 + pi / 18) ** 3 * (1 - 2 * sin(x / 12 + pi / 36) ** 2) ** 3 + 6 * sin(x / 6 + pi / 18) * (1 - 2 * sin(x / 12 + pi / 36) ** 2)) ** 2 + sin(x - pi / 6) ** 2 = (-32*(1 - 2*sin(x/12 + pi/36)**2)**3*sin(x/6 + pi/18)**3 + 6*(1 - 2*sin(x/12 + pi/36)**2)*sin(x/6 + pi/18))**2 + sin(x - pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x/6 + pi/18) = 1 - 2 * sin(x/12 + pi/36) ** 2,
{
have : cos(x/6 + pi/18) = cos(2*(x/12 + pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : ((-4) * (2 * sin(x / 6 + pi / 18) * cos(x / 6 + pi / 18)) ** 3 + 3 * (2 * sin(x / 6 + pi / 18) * cos(x / 6 + pi / 18))) ** 2 + sin(x - pi / 6) ** 2 = (-32*sin(x/6 + pi/18)**3*cos(x/6 + pi/18)**3 + 6*sin(x/6 + pi/18)*cos(x/6 + pi/18))**2 + sin(x - pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/3 + pi/9) = 2 * sin(x/6 + pi/18) * cos(x/6 + pi/18),
{
have : sin(x/3 + pi/9) = sin(2*(x/6 + pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi / 6) ** 2 + ((-4) * sin(x / 3 + pi / 9) ** 3 + 3 * sin(x / 3 + pi / 9)) ** 2 = (-4*sin(x/3 + pi/9)**3 + 3*sin(x/3 + pi/9))**2 + sin(x - pi/6)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/3) = -4 * sin(x/3 + pi/9) ** 3 + 3 * sin(x/3 + pi/9),
{
have : sin(x + pi/3) = sin(3*(x/3 + pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi/6)**2 = 1/2 - cos(2*x - pi/3)/2,
{
have : cos(2*x - pi/3) = cos(2*(x - pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : sin(x + pi/3)**2 = 1/2 - cos(2*x + 2*pi/3)/2,
{
have : cos(2*x + 2*pi/3) = cos(2*(x + pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(2*x + 2*pi/3) = -cos(2*x - pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*x + 2*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_124_VKAO_extend (h0 : cos(pi/12)≠ 0) (h1 : (2*cos(pi/12))≠ 0) : sin(pi/6)*cos(5*pi/12)/(2*cos(pi/12)) + ((1 - 2*sin(19*pi/24)**2)*sin(-pi) + sin(19*pi/12)*cos(-pi))*cos(pi/12)=1:=
begin
have : sin(pi / 6) / (2 * cos(pi / 12)) * cos(5 * pi / 12) + ((1 - 2 * sin(19 * pi / 24) ** 2) * sin(-pi) + sin(19 * pi / 12) * cos(-pi)) * cos(pi / 12) = sin(pi/6)*cos(5*pi/12)/(2*cos(pi/12)) + ((1 - 2*sin(19*pi/24)**2)*sin(-pi) + sin(19*pi/12)*cos(-pi))*cos(pi/12),
{
field_simp at *,
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
have : sin(pi / 12) * cos(5 * pi / 12) + (sin(-pi) * (1 - 2 * sin(19 * pi / 24) ** 2) + sin(19 * pi / 12) * cos(-pi)) * cos(pi / 12) = sin(pi/12)*cos(5*pi/12) + ((1 - 2*sin(19*pi/24)**2)*sin(-pi) + sin(19*pi/12)*cos(-pi))*cos(pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(19*pi/12) = 1 - 2 * sin(19*pi/24) ** 2,
{
have : cos(19*pi/12) = cos(2*(19*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * cos(5 * pi / 12) + (sin(19 * pi / 12) * cos(-pi) + sin(-pi) * cos(19 * pi / 12)) * cos(pi / 12) = sin(pi/12)*cos(5*pi/12) + (sin(-pi)*cos(19*pi/12) + sin(19*pi/12)*cos(-pi))*cos(pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) = sin(19*pi/12) * cos(-pi) + sin(-pi) * cos(19*pi/12),
{
have : sin(7*pi/12) = sin((19*pi/12) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/12) = sin(5*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12) = sin(pi/2),
{
have : sin(pi/2) = sin((pi/12) + (5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_two,
end


lemma Trigo_2_125_NXBJ_extend(h0 : cos(pi/20) ≠ 0) (h1 : cos(17*pi/60) ≠ 0)  (h2 : cos(17*pi/60)≠ 0) (h3 : cos(pi/20)≠ 0) (h4 : tan((17*pi/60)-(pi/20))≠ 0) (h5 : 1+tan(17*pi/60)*tan(pi/20)≠ 0) (h6 : (-((tan(17*pi/60)-tan(pi/20))/tan(7*pi/30)-1)+1)≠ 0) (h7 : (-(-tan(pi/20)+tan(17*pi/60))/tan(7*pi/30)+2)≠ 0) (h8 : tan(7*pi/30)≠ 0) (h9 : ((-tan(17*pi/60)-tan(539*pi/20))/tan(7*pi/30)+2)≠ 0) (h10 : (-(- -tan(539*pi/20)+tan(17*pi/60))/tan(7*pi/30)+2)≠ 0) (h11 : ((-tan(17*pi/60)-tan(759*pi/20))/tan(7*pi/30)+2)≠ 0) : (-tan(759*pi/20) + tan(17*pi/60))/((-tan(17*pi/60) - tan(759*pi/20))/tan(7*pi/30) + 2)=sqrt(3):=
begin
have : tan(539*pi/20) = tan(759*pi/20),
{
rw tan_eq_tan_add_int_mul_pi (539*pi/20) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-tan(539 * pi / 20) + tan(17 * pi / 60)) / (-(- -tan(539 * pi / 20) + tan(17 * pi / 60)) / tan(7 * pi / 30) + 2) = (-tan(539*pi/20) + tan(17*pi/60))/((-tan(17*pi/60) - tan(539*pi/20))/tan(7*pi/30) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/20) = -tan(539*pi/20),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/20) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 20) + tan(17 * pi / 60)) / (-((tan(17 * pi / 60) - tan(pi / 20)) / tan(7 * pi / 30) - 1) + 1) = (tan(pi/20) + tan(17*pi/60))/(-(-tan(pi/20) + tan(17*pi/60))/tan(7*pi/30) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(17*pi/60) * tan(pi/20) = ( tan(17*pi/60) - tan(pi/20) ) / tan(7*pi/30) - 1,
{
rw tan_mul_tan,
have : tan((17*pi/60) - (pi/20)) = tan(7*pi/30),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -(tan(17*pi/60) * tan(pi/20)) = -tan(pi/20)*tan(17*pi/60),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan(pi/20) + tan(17*pi/60))/(-tan(pi/20)*tan(17*pi/60) + 1) = tan(pi/3),
{
have : tan(pi/3) = tan((pi/20) + (17*pi/60)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_add,
field_simp,
ring_exp,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
end


lemma Trigo_2_126_AKLW_extend(h0 : cos(x) + cos(2*x) ≠ 0) (h1 : cos(3*x/2) ≠ 0) (h2 : cos(x/2) ≠ 0) (h3 : cos(x)/2 + cos(2*x)/2 ≠ 0)  (h4 : (-sin(2*x+107*pi/2)+cos(x))≠ 0) (h5 : (cos(x)+-sin(2*x+107*pi/2))≠ 0) (h6 : (-sin(2*x+107*pi/2)+cos(-x+186*pi))≠ 0) (h7 : sin(-x + 186*pi)≠ 0) (h8 : (sin(-2*x+372*pi)/(2*sin(-x+186*pi))-sin(2*x+107*pi/2))≠ 0) (h9 : (2*sin(-x+186*pi))≠ 0) (h10 : (-sin(2*x+107*pi/2)+sin((-2)*x+372*pi)/(2*sin(-x+186*pi)))≠ 0) : -tan(x/2) + tan(3*x/2)=2*sin(x)/(sin(-2*x + 372*pi)/(2*sin(-x + 186*pi)) - sin(2*x + 107*pi/2)):=
begin
have : 2 * sin(x) / (-sin(2 * x + 107 * pi / 2) + sin((-2) * x + 372 * pi) / (2 * sin(-x + 186 * pi))) = 2*sin(x)/(sin(-2*x + 372*pi)/(2*sin(-x + 186*pi)) - sin(2*x + 107*pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(-x + 186*pi) = sin(-2*x + 372*pi) / ( 2 * sin(-x + 186*pi) ),
{
have : sin(-2*x + 372*pi) = sin(2*(-x + 186*pi)),
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
have : cos(x) = cos(-x + 186*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * sin(x) / (cos(x) + -sin(2 * x + 107 * pi / 2)) = 2*sin(x)/(-sin(2*x + 107*pi/2) + cos(x)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*x) = -sin(2*x + 107*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*x) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : -tan(x/2) + tan(3*x/2) = sin(x)/(cos(x/2)*cos(3*x/2)),
{
rw neg_add_eq_sub,
rw tan_sub_tan',
have : sin((3*x/2) - (x/2)) = sin(x),
{
apply congr_arg,
ring,
},
rw this,
field_simp,
left,
ring,
repeat {assumption},
},
rw this,
have : cos(x/2)*cos(3*x/2) = cos(x)/2 + cos(2*x)/2,
{
rw mul_comm,
rw cos_mul_cos,
have : cos((3*x/2) + (x/2)) = cos(2*x),
{
apply congr_arg,
ring,
},
rw this,
have : cos((3*x/2) - (x/2)) = cos(x),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(x)/(cos(x)/2 + cos(2*x)/2) = 2*sin(x)/(cos(x) + cos(2*x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
end


lemma Trigo_0_127_ZUNT_extend(h0 : cos(x)**2 ≠ 0)  (h1 : cos(x)≠ 0) : sin(x + 71*pi)**5/cos(x)**2 - sin(x + 71*pi)*cos(x)**2 + 2*sin(x + 71*pi) - sin(x + 71*pi)/cos(x)**2=0:=
begin
have : cos(x) ** 2 * -sin(x + 71 * pi) - 2 * -sin(x + 71 * pi) - (-sin(x + 71 * pi)) ** 5 / cos(x) ** 2 + -sin(x + 71 * pi) / cos(x) ** 2 = sin(x + 71*pi)**5/cos(x)**2 - sin(x + 71*pi)*cos(x)**2 + 2*sin(x + 71*pi) - sin(x + 71*pi)/cos(x)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 101*pi/2) = -sin(x + 71*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 101*pi/2) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 207*pi/2) = cos(-x + 101*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x + 207*pi/2) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(x + 207 * pi / 2) ** 5 / cos(x) ** 2 + cos(x + 207 * pi / 2) * cos(x) ** 2 - 2 * cos(x + 207 * pi / 2) + cos(x + 207 * pi / 2) / cos(x) ** 2 = cos(x)**2*cos(x + 207*pi/2) - 2*cos(x + 207*pi/2) - cos(x + 207*pi/2)**5/cos(x)**2 + cos(x + 207*pi/2)/cos(x)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = cos(x + 207*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x)**5/cos(x)**2 + sin(x)*cos(x)**2 = (-sin(x)**5 + sin(x)*cos(x)**4)/cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : -sin(x)**5 + sin(x)*cos(x)**4 = (-sin(x)**4 + cos(x)**4)*sin(x),
{
ring_exp,
},
rw this,
have : -sin(x)**4 + cos(x)**4 = (-sin(x)**2 + cos(x)**2)*(sin(x)**2 + cos(x)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
simp,
rw sub_eq_add_neg,
rw add_assoc,
rw ← sub_eq_neg_add (sin(x) / cos(x) ** 2) (2 * sin(x)),
rw ← add_sub_assoc,
have : (-sin(x)**2 + cos(x)**2)*sin(x)/cos(x)**2 + sin(x)/cos(x)**2 = ((-sin(x)**2 + cos(x)**2)*sin(x) + sin(x))/cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : (-sin(x)**2 + cos(x)**2)*sin(x) + sin(x) = (-sin(x)**2 + cos(x)**2 + 1)*sin(x),
{
ring_exp,
},
rw this,
rw sin_sq,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_128_ESIQ_extend : cos(2527*pi/12)**2 + 4*sin(pi/24)**2*cos(pi/24)**2 - 2*sin(pi/24)*cos(pi/24)*cos(2527*pi/12)=3/2 - 3*sqrt(3)/4:=
begin
have : -(2 * sin(pi / 24) * cos(pi / 24)) * cos(2527 * pi / 12) + cos(2527 * pi / 12) ** 2 + (2 * sin(pi / 24) * cos(pi / 24)) ** 2 = cos(2527*pi/12)**2 + 4*sin(pi/24)**2*cos(pi/24)**2 - 2*sin(pi/24)*cos(pi/24)*cos(2527*pi/12),
{
field_simp at *,
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
have : sin(pi / 12) * -cos(2527 * pi / 12) + (-cos(2527 * pi / 12)) ** 2 + sin(pi / 12) ** 2 = -sin(pi/12)*cos(2527*pi/12) + cos(2527*pi/12)**2 + sin(pi/12)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(907*pi/12) = -cos(2527*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (907*pi/12) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) ** 2 + sin(pi / 12) * cos(907 * pi / 12) + cos(907 * pi / 12) ** 2 = sin(pi/12)*cos(907*pi/12) + cos(907*pi/12)**2 + sin(pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = cos(907*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/12) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
ring_nf,
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
rw cos_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_0_129_COJG_extend(h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0)  (h2 : (sin(pi/24)*(-sin(5*pi/24)*sin(-pi/6)+cos(5*pi/24)*cos(-pi/6)))≠ 0) (h3 : ((-sin(-pi/6)*sin(5*pi/24)+cos(-pi/6)*cos(5*pi/24))*sin(pi/24))≠ 0) (h4 : cos((pi/6)/2)≠ 0) (h5 : sin(pi/6)≠ 0) : 2*(1 - cos(pi/6))/sin(pi/6) + (-1 + 2*cos(pi/24)**2)/((-sin(-pi/6)*sin(5*pi/24) + cos(-pi/6)*cos(5*pi/24))*sin(pi/24))=8:=
begin
have : 2 * ((1 - cos(pi / 6)) / sin(pi / 6)) + (-1 + 2 * cos(pi / 24) ** 2) / ((-sin(-pi / 6) * sin(5 * pi / 24) + cos(-pi / 6) * cos(5 * pi / 24)) * sin(pi / 24)) = 2*(1 - cos(pi/6))/sin(pi/6) + (-1 + 2*cos(pi/24)**2)/((-sin(-pi/6)*sin(5*pi/24) + cos(-pi/6)*cos(5*pi/24))*sin(pi/24)),
{
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
have : 2 * tan(pi / 12) + (1 - 2 * (1 - cos(pi / 24) ** 2)) / ((-sin(-pi / 6) * sin(5 * pi / 24) + cos(-pi / 6) * cos(5 * pi / 24)) * sin(pi / 24)) = 2*tan(pi/12) + (-1 + 2*cos(pi/24)**2)/((-sin(-pi/6)*sin(5*pi/24) + cos(-pi/6)*cos(5*pi/24))*sin(pi/24)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/24) ** 2 = 1 - cos(pi/24) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : -(2 * sin(pi / 24) ** 2 - 1) / (sin(pi / 24) * (-sin(5 * pi / 24) * sin(-pi / 6) + cos(5 * pi / 24) * cos(-pi / 6))) + 2 * tan(pi / 12) = 2*tan(pi/12) + (1 - 2*sin(pi/24)**2)/((-sin(-pi/6)*sin(5*pi/24) + cos(-pi/6)*cos(5*pi/24))*sin(pi/24)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -sin(5*pi/24) * sin(-pi/6) + cos(5*pi/24) * cos(-pi/6),
{
have : cos(pi/24) = cos((5*pi/24) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/24)*cos(pi/24) = sin(pi/12)/2,
{
have : sin(pi/12) = 2*sin(pi/24)*cos(pi/24),
{
have : sin(pi/12) = sin(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
have : 2*sin(pi/24)**2 - 1 = -cos(pi/12),
{
have : cos(pi/12) = 1 - 2*sin(pi/24)**2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
linarith,
},
rw this,
rw neg_neg,
have : cos(pi/12)/(sin(pi/12)/2) = 2*cos(pi/12)/sin(pi/12),
{
field_simp,
ring,
},
rw this,
have :2*cos(pi/12)/sin(pi/12) + 2*(sin(pi/12)/cos(pi/12)) = (2*sin(pi/12)**2 + 2*cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : 2*sin(pi/12)**2 + 2*cos(pi/12)**2 = 2,
{
have : sin(pi/12)**2 + cos(pi/12)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_130_UBYA_extend(h0 : sin(x) ≠ 0)  (h1 : tan(x) ≠ 0) (h2 : sin(-x-pi)≠ 0) (h3 : sin(x/2 + 63*pi/2)≠ 0) (h4 : (2*sin(x/2+63*pi/2))≠ 0) (h5 : (4*sin(x/2+63*pi/2)**2)≠ 0) : (sin(x/2 + 63*pi/2)**2 - sin(x + 63*pi)**2/(4*sin(x/2 + 63*pi/2)**2))*sin(pi - x)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi)=-cos(x):=
begin
have : -(-sin(x / 2 + 63 * pi / 2) ** 2 + (sin(x + 63 * pi) / (2 * sin(x / 2 + 63 * pi / 2))) ** 2) * sin(pi - x) * tan(-x - pi) * tan(-x + 3 * pi / 2) / sin(-x - pi) = (sin(x/2 + 63*pi/2)**2 - sin(x + 63*pi)**2/(4*sin(x/2 + 63*pi/2)**2))*sin(pi - x)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x/2 + 63*pi/2) = sin(x + 63*pi) / ( 2 * sin(x/2 + 63*pi/2) ),
{
have : sin(x + 63*pi) = sin(2*(x/2 + 63*pi/2)),
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
have : -sin(pi - x) * (-sin(x / 2 + 63 * pi / 2) ** 2 + cos(x / 2 + 63 * pi / 2) ** 2) * tan(-x - pi) * tan(-x + 3 * pi / 2) / sin(-x - pi) = -(-sin(x/2 + 63*pi/2)**2 + cos(x/2 + 63*pi/2)**2)*sin(pi - x)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 63*pi) = -sin(x/2 + 63*pi/2) ** 2 + cos(x/2 + 63*pi/2) ** 2,
{
have : cos(x + 63*pi) = cos(2*(x/2 + 63*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) * -cos(x + 63 * pi) * tan(-x - pi) * tan(-x + 3 * pi / 2) / sin(-x - pi) = -sin(pi - x)*cos(x + 63*pi)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = -cos(x + 63*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x + 2*pi) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(-x),
{
rw cos_eq_cos_add_int_mul_two_pi (-x + 2*pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x - pi) = -tan(x + pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(x + pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x + 3*pi/2) = 1/tan(x),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x - pi) = -sin(x + pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x - pi) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_131_OLPJ_extend(h0 : cos(x)**2 ≠ 0)  (h1 : cos(x/2)≠ 0) (h2 : (1-tan(x/2)**2)≠ 0) : (1 + 4*tan(x/2)**2/(1 - tan(x/2)**2)**2)*(1 - cos(-2*x - 33*pi))=2:=
begin
have : (1 + 4 * tan(x / 2) ** 2 / (1 - tan(x / 2) ** 2) ** 2) * (-cos((-2) * x - 33 * pi) + 1) = (1 + 4*tan(x/2)**2/(1 - tan(x/2)**2)**2)*(1 - cos(-2*x - 33*pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x + 122*pi) = -cos(-2*x - 33*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*x + 122*pi) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = cos(2*x + 122*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*x) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(2 * x) + 1) * ((2 * tan(x / 2) / (1 - tan(x / 2) ** 2)) ** 2 + 1) = (1 + 4*tan(x/2)**2/(1 - tan(x/2)**2)**2)*(cos(2*x) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x) = 2 * tan(x/2) / ( 1 - tan(x/2) ** 2 ),
{
have : tan(x) = tan(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = 2*cos(x)**2 - 1,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
end


lemma Trigo_0_132_YSVW_extend (h0 : sin(1)≠ 0) (h1 : (4*sin(1)**2)≠ 0) (h2 : (2*sin(1))≠ 0) (h3 : (4*sin(-1+147*pi)**2)≠ 0) (h4 : cos(-1 + 147*pi)≠ 0) (h5 : (2*cos(-1+147*pi))≠ 0) (h6 : (4*cos(-1+147*pi)**2)≠ 0) (h7 : sin(-2+294*pi)≠ 0) (h8 : (4*(sin(-2+294*pi)/(2*cos(-1+147*pi)))**2)≠ 0) : sin(2)**2*cos(-1 + 147*pi)**2/sin(-2 + 294*pi)**2 + sin(-2 + 294*pi)**2/(4*cos(-1 + 147*pi)**2)=1:=
begin
have : sin(2) ** 2 / (4 * (sin(-2 + 294 * pi) / (2 * cos(-1 + 147 * pi))) ** 2) + (sin(-2 + 294 * pi) / (2 * cos(-1 + 147 * pi))) ** 2 = sin(2)**2*cos(-1 + 147*pi)**2/sin(-2 + 294*pi)**2 + sin(-2 + 294*pi)**2/(4*cos(-1 + 147*pi)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-1 + 147*pi) = sin(-2 + 294*pi) / ( 2 * cos(-1 + 147*pi) ),
{
have : sin(-2 + 294*pi) = sin(2*(-1 + 147*pi)),
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
have : sin(1) = sin(-1 + 147*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (1) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1) ** 2 + (sin(2) / (2 * sin(1))) ** 2 = sin(2)**2/(4*sin(1)**2) + sin(1)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1) = sin(2) / ( 2 * sin(1) ),
{
have : sin(2) = sin(2*(1)),
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
rw sin_sq_add_cos_sq,
end


lemma Trigo_0_133_SMIB_extend(h0 : sin(pi/9) ≠ 0)  : (-1 + 2*cos(2*pi/9)**2)*(-sin(pi/18)**2 + cos(pi/18)**2)*sin(2741*pi/18)=1/8:=
begin
have : (-sin(pi / 18) ** 2 + cos(pi / 18) ** 2) * sin(2741 * pi / 18) * (2 * cos(2 * pi / 9) ** 2 - 1) = (-1 + 2*cos(2*pi/9)**2)*(-sin(pi/18)**2 + cos(pi/18)**2)*sin(2741*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = 2 * cos(2*pi/9) ** 2 - 1,
{
have : cos(4*pi/9) = cos(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(2741 * pi / 18) * (-sin(pi / 18) ** 2 + cos(pi / 18) ** 2) * cos(4 * pi / 9) = (-sin(pi/18)**2 + cos(pi/18)**2)*sin(2741*pi/18)*cos(4*pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
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
have : cos(pi / 9) * sin(2741 * pi / 18) * cos(4 * pi / 9) = sin(2741*pi/18)*cos(pi/9)*cos(4*pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = sin(2741*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/9) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw div_mul_eq_mul_div,
rw this,
rw div_mul_eq_mul_div,
rw div_mul_eq_mul_div,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_0_134_OSKG_extend : -sin(463*pi/12)*cos(pi/12) - sin(-529*pi/12)*sin(pi/12)=-sqrt(3)/2:=
begin
have : -sin(463 * pi / 12) * cos(pi / 12) + sin(pi / 12) * -sin((-529) * pi / 12) = -sin(463*pi/12)*cos(pi/12) - sin(-529*pi/12)*sin(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2107*pi/12) = -sin(-529*pi/12),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2107*pi/12) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = cos(2107*pi/12),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/12) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * cos(5 * pi / 12) - sin(463 * pi / 12) * cos(pi / 12) = -sin(463*pi/12)*cos(pi/12) + sin(pi/12)*cos(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = sin(463*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/12) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)*cos(5*pi/12) - sin(5*pi/12)*cos(pi/12) = sin(-pi/3),
{
have : sin(-pi/3) = sin((pi/12) - (5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(-pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
field_simp,
end


lemma Trigo_0_135_AVUS_extend(h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0)  (h2 : cos((pi/6)/2)≠ 0) (h3 : (1-cos(pi/6))≠ 0) (h4 : ((1-cos(pi/6))/sin(pi/6))≠ 0) (h5 : sin(pi/6)≠ 0) (h6 : (1-sin(397*pi/3))≠ 0) (h7 : (-3*sin(397*pi/9)+4*sin(397*pi/9)**3+1)≠ 0) (h8 : (1-((-4)*sin(397*pi/9)**3+3*sin(397*pi/9)))≠ 0) : (-3*sin(397*pi/9) + 4*sin(397*pi/9)**3 + 1)/sin(pi/6) + sin(pi/6)/(-3*sin(397*pi/9) + 4*sin(397*pi/9)**3 + 1)=4:=
begin
have : (1 - ((-4) * sin(397 * pi / 9) ** 3 + 3 * sin(397 * pi / 9))) / sin(pi / 6) + sin(pi / 6) / (1 - ((-4) * sin(397 * pi / 9) ** 3 + 3 * sin(397 * pi / 9))) = (-3*sin(397*pi/9) + 4*sin(397*pi/9)**3 + 1)/sin(pi/6) + sin(pi/6)/(-3*sin(397*pi/9) + 4*sin(397*pi/9)**3 + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(397*pi/3) = -4 * sin(397*pi/9) ** 3 + 3 * sin(397*pi/9),
{
have : sin(397*pi/3) = sin(3*(397*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = sin(397*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos(pi / 6)) / sin(pi / 6) + 1 / ((1 - cos(pi / 6)) / sin(pi / 6)) = (1 - cos(pi/6))/sin(pi/6) + sin(pi/6)/(1 - cos(pi/6)),
{
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
rw tan_eq_sin_div_cos,
rw one_div_div,
have : sin(pi/12)/cos(pi/12) + cos(pi/12)/sin(pi/12) = (sin(pi/12)**2 + cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_136_TRLV_extend (h0 : cos(593*pi/12)≠ 0) (h1 : (2*cos(593*pi/12))≠ 0) (h2 : (2*cos(2825*pi/12))≠ 0) : sin(pi/12)*sin(593*pi/6)/(2*cos(2825*pi/12))=-1/4:=
begin
have : cos(593*pi/12) = cos(2825*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (593*pi/12) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * (sin(593 * pi / 6) / (2 * cos(593 * pi / 12))) = sin(pi/12)*sin(593*pi/6)/(2*cos(593*pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(593*pi/12) = sin(593*pi/6) / ( 2 * cos(593*pi/12) ),
{
have : sin(593*pi/6) = sin(2*(593*pi/12)),
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
have : cos(11*pi/12) = sin(593*pi/12),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (11*pi/12) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/12) = -cos(pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_neg,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_137_ZVTE_extend(h0: sin(x) ≠ 0) (h1: cos(x) ≠ 0) (h2 : sin(2*x)≠ 0) (h3 : (sin(2*x-pi)*cos(pi)+sin(pi)*cos(2*x-pi))≠ 0) : tan(x)=(cos(-2*x + 29*pi) + 1)/(sin(2*x - pi)*cos(pi) + sin(pi)*cos(2*x - pi)):=
begin
have : (cos((-2) * x + 29 * pi) + 1) / (sin(2 * x - pi) * cos(pi) + sin(pi) * cos(2 * x - pi)) = (cos(-2*x + 29*pi) + 1)/(sin(2*x - pi)*cos(pi) + sin(pi)*cos(2*x - pi)),
{
field_simp at *,
},
have : sin(2*x) = sin(2*x - pi) * cos(pi) + sin(pi) * cos(2*x - pi),
{
have : sin(2*x) = sin((2*x - pi) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_rhs, rw ← this,},
have : (cos((-2) * x + 29 * pi) + 1) / sin(2 * x) = (cos(-2*x + 29*pi) + 1)/sin(2*x),
{
field_simp at *,
},
have : cos(2*x + 25*pi) = cos(-2*x + 29*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*x + 25*pi) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (1 - -cos(2 * x + 25 * pi)) / sin(2 * x) = (cos(2*x + 25*pi) + 1)/sin(2*x),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*x) = -cos(2*x + 25*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*x) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*x) = 1 - 2*sin(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring,
end


lemma Trigo_0_138_GYRF_extend : -sin(-3008*pi/45)*cos(-3008*pi/45) - sin(803*pi/6)/2 + cos(13*pi/180)*cos(47*pi/180)=1/2:=
begin
have : -(2 * sin((-3008) * pi / 45) * cos((-3008) * pi / 45)) / 2 - sin(803 * pi / 6) / 2 + cos(13 * pi / 180) * cos(47 * pi / 180) = -sin(-3008*pi/45)*cos(-3008*pi/45) - sin(803*pi/6)/2 + cos(13*pi/180)*cos(47*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-6016*pi/45) = 2 * sin(-3008*pi/45) * cos(-3008*pi/45),
{
have : sin(-6016*pi/45) = sin(2*(-3008*pi/45)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : -(sin((-6016) * pi / 45) / 2 + sin(803 * pi / 6) / 2) + cos(13 * pi / 180) * cos(47 * pi / 180) = -sin(-6016*pi/45)/2 - sin(803*pi/6)/2 + cos(13*pi/180)*cos(47*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) * cos(24077*pi/180) = sin(-6016*pi/45) / 2 + sin(803*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((13*pi/180) + (24077*pi/180)) = sin(803*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((13*pi/180) - (24077*pi/180)) = sin(-6016*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(sin(13*pi/180) * cos(24077*pi/180)) = -sin(13*pi/180)*cos(24077*pi/180),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(13 * pi / 180) * -cos(24077 * pi / 180) + cos(13 * pi / 180) * cos(47 * pi / 180) = -sin(13*pi/180)*cos(24077*pi/180) + cos(13*pi/180)*cos(47*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(137*pi/180) = -cos(24077*pi/180),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (137*pi/180) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(47*pi/180) = sin(137*pi/180),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (47*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_comm,
have : sin(137*pi/180)*cos(13*pi/180) + sin(13*pi/180)*cos(137*pi/180) = sin(5*pi/6),
{
have : sin(5*pi/6) = sin((13*pi/180) + (137*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
have : sin(5*pi/6) = sin(pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_0_139_FGHY_extend : (-2*sin(pi/24)**2 + sin(-805*pi/12) + 1)**2=3/2:=
begin
have : ((-2) * sin(pi / 24) ** 2 + sin((-805) * pi / 12) + 1) ** 2 = (-2*sin(pi/24)**2 + sin(-805*pi/12) + 1)**2,
{
field_simp at *,
},
have : sin(961*pi/12) = sin(-805*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (961*pi/12) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-2) * sin(pi / 24) ** 2 + sin(961 * pi / 12) + 1) ** 2 = (-2*sin(pi/24)**2 + sin(961*pi/12) + 1)**2,
{
field_simp at *,
},
have : sin(pi/12) = sin(961*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 12) + (1 - 2 * sin(pi / 24) ** 2)) ** 2 = (-2*sin(pi/24)**2 + sin(pi/12) + 1)**2,
{
field_simp at *,
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
have : (sin(pi/12) + cos(pi/12))**2 = sin(pi/12)**2 + 2*sin(pi/12)*cos(pi/12) + cos(pi/12)**2,
{
ring_exp,
},
rw this,
rw add_right_comm,
rw sin_sq_add_cos_sq,
have : 2*sin(pi/12)*cos(pi/12) = sin(pi/6),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_0_140_QAXJ_extend : -3 + 6*sin(pi/18)**2 - sqrt(3)*cos(629*pi/6) + 4*(1 - 2*sin(pi/18)**2)**3=2:=
begin
have : (-3) * (1 - 2 * sin(pi / 18) ** 2) - sqrt 3 * cos(629 * pi / 6) + 4 * (1 - 2 * sin(pi / 18) ** 2) ** 3 = -3 + 6*sin(pi/18)**2 - sqrt(3)*cos(629*pi/6) + 4*(1 - 2*sin(pi/18)**2)**3,
{
field_simp at *,
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
have : (-3) * cos(pi / 9) + sqrt 3 * -cos(629 * pi / 6) + 4 * cos(pi / 9) ** 3 = -3*cos(pi/9) - sqrt(3)*cos(629*pi/6) + 4*cos(pi/9)**3,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/3) = -cos(629*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/3) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(2 * pi / 3) + (4 * cos(pi / 9) ** 3 - 3 * cos(pi / 9)) = -3*cos(pi/9) + sqrt(3)*sin(2*pi/3) + 4*cos(pi/9)**3,
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
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
ring_exp,
rw sq_sqrt,
norm_num,
repeat {linarith},
end


lemma Trigo_0_141_BVJX_extend(h0 : cos(x)**2 ≠ 0)  : (-(-sin(-pi/6)*sin(x/2 + 470*pi/3) + cos(-pi/6)*cos(x/2 + 470*pi/3))**2 + cos(x/2)**2)**2*(tan(x)**2 + 1)=1:=
begin
have : (cos(x / 2) ** 2 - (-sin(x / 2 + 470 * pi / 3) * sin(-pi / 6) + cos(x / 2 + 470 * pi / 3) * cos(-pi / 6)) ** 2) ** 2 * (tan(x) ** 2 + 1) = (-(-sin(-pi/6)*sin(x/2 + 470*pi/3) + cos(-pi/6)*cos(x/2 + 470*pi/3))**2 + cos(x/2)**2)**2*(tan(x)**2 + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x/2 + 313*pi/2) = -sin(x/2 + 470*pi/3) * sin(-pi/6) + cos(x/2 + 470*pi/3) * cos(-pi/6),
{
have : cos(x/2 + 313*pi/2) = cos((x/2 + 470*pi/3) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-(-cos(x / 2 + 313 * pi / 2)) ** 2 + cos(x / 2) ** 2) ** 2 * (tan(x) ** 2 + 1) = (cos(x/2)**2 - cos(x/2 + 313*pi/2)**2)**2*(tan(x)**2 + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/2) = -cos(x/2 + 313*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (x/2) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(x) ** 2 + 1) * (-sin(x / 2) ** 2 + cos(x / 2) ** 2) ** 2 = (-sin(x/2)**2 + cos(x/2)**2)**2*(tan(x)**2 + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -sin(x/2) ** 2 + cos(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw div_pow,
have : (sin(x)**2/cos(x)**2 + 1)*cos(x)**2 = sin(x)**2 + cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
rw sin_sq_add_cos_sq,
end


lemma Trigo_0_142_NHYP_extend : -cos(-2*pi/15)/2 - cos(2*pi/3)/2 - sin(1639*pi/15)*sin(873*pi/5)=1/2:=
begin
have : -cos((-2) * pi / 15) / 2 - cos(2 * pi / 3) / 2 - sin(1639 * pi / 15) * sin(873 * pi / 5) = -cos(-2*pi/15)/2 - cos(2*pi/3)/2 - sin(1639*pi/15)*sin(873*pi/5),
{
field_simp at *,
},
have : cos(pi/10) = sin(873*pi/5),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/10) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos((-2) * pi / 15) / 2 - cos(2 * pi / 3) / 2 + cos(pi / 10) * -sin(1639 * pi / 15) = -cos(-2*pi/15)/2 - cos(2*pi/3)/2 - sin(1639*pi/15)*cos(pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/30) = -sin(1639*pi/15),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/30) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 10) * cos(7 * pi / 30) - (cos((-2) * pi / 15) / 2 + cos(2 * pi / 3) / 2) = -cos(-2*pi/15)/2 - cos(2*pi/3)/2 + cos(pi/10)*cos(7*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/15) * cos(2*pi/5) = cos(-2*pi/15) / 2 + cos(2*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((4*pi/15) + (2*pi/5)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((4*pi/15) - (2*pi/5)) = cos(-2*pi/15),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(4*pi/15) * cos(2*pi/5)) = cos(4*pi/15)*cos(2*pi/5),
{
ring,
},
have : cos(2*pi/5) = sin(pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/5) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(4*pi/15) = sin(7*pi/30),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/15) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_comm (sin(7*pi/30)) (sin(pi/10)),
have : cos(pi/10)*cos(7*pi/30) - sin(pi/10)*sin(7*pi/30) = cos(pi/3),
{
have : cos(pi/3) = cos((pi/10) + (7*pi/30)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
},
rw this,
rw cos_pi_div_three,
end


lemma Trigo_0_143_RDGT_extend(h0 : sin(2*pi/9) ≠ 0) (h1 : cos(pi/9) ≥ 0)  (h2 : cos(5*pi/18)≠ 0) (h3 : cos(1921*pi/18)≠ 0) (h4 : -cos(1921*pi/18)≠ 0) : sqrt(cos(2*pi/9) + 1)*cos(299*pi/18)/cos(1921*pi/18)=sqrt(2)/2:=
begin
have : -sqrt (cos(2 * pi / 9) + 1) * cos(299 * pi / 18) / -cos(1921 * pi / 18) = sqrt(cos(2*pi/9) + 1)*cos(299*pi/18)/cos(1921*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/18) = -cos(1921*pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/18) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(71*pi/9) = cos(299*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (71*pi/9) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (cos(2 * pi / 9) + 1) * -sin(71 * pi / 9) / cos(5 * pi / 18) = -sqrt(cos(2*pi/9) + 1)*sin(71*pi/9)/cos(5*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = -sin(71*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/9) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = 2*cos(pi/9)**2 - 1,
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
simp,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h1,
rw mul_assoc,
rw mul_comm (cos(pi/9)) (sin(pi/9)),
have : sin(pi/9)*cos(pi/9) = sin(2*pi/9)/2,
{
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(5*pi/18) = sin(2*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_0_144_QRGX_extend : cos(332*pi/3)/2 - sin(47*pi/6)/2 + cos(122*pi)/2 + sin(13*pi/2)/2=1:=
begin
have : cos(332 * pi / 3) / 2 + cos(122 * pi) / 2 + (-sin(47 * pi / 6) / 2 + sin(13 * pi / 2) / 2) = cos(332*pi/3)/2 - sin(47*pi/6)/2 + cos(122*pi)/2 + sin(13*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-2*pi/3) * cos(43*pi/6) = -sin(47*pi/6) / 2 + sin(13*pi/2) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((43*pi/6) + (-2*pi/3)) = sin(13*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : sin((43*pi/6) - (-2*pi/3)) = sin(47*pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-2*pi/3) * cos(43*pi/6)) = sin(-2*pi/3)*cos(43*pi/6),
{
ring,
},
have : cos(122 * pi) / 2 + cos(332 * pi / 3) / 2 + sin((-2) * pi / 3) * cos(43 * pi / 6) = cos(332*pi/3)/2 + cos(122*pi)/2 + sin(-2*pi/3)*cos(43*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(349*pi/3) * cos(-17*pi/3) = cos(122*pi) / 2 + cos(332*pi/3) / 2,
{
rw cos_mul_cos,
have : cos((349*pi/3) + (-17*pi/3)) = cos(332*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((349*pi/3) - (-17*pi/3)) = cos(122*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(349*pi/3) * cos(-17*pi/3)) = cos(-17*pi/3)*cos(349*pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(349 * pi / 3) * cos((-17) * pi / 3) + sin((-2) * pi / 3) * cos(43 * pi / 6) = cos(-17*pi/3)*cos(349*pi/3) + sin(-2*pi/3)*cos(43*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-35*pi/6) = cos(349*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-35*pi/6) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-35*pi/6) = sin(pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-35*pi/6) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-17*pi/3) = cos(pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (-17*pi/3) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-2*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(43*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (43*pi/6) (-4),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_three,
rw sin_pi_div_three,
rw cos_pi_div_six,
ring_exp,
rw sq_sqrt,
norm_num,
repeat {linarith},
end


lemma Trigo_0_145_STWJ_extend : (-1 + 2*sin(11*pi/72)**2)*sin(pi/18) + sin(4*pi/9)*cos(1663*pi/36)=sqrt(2)/2:=
begin
have : cos(4673*pi/36) = cos(1663*pi/36),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (4673*pi/36) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - 2 * sin(11 * pi / 72) ** 2) * sin(pi / 18) + sin(4 * pi / 9) * cos(4673 * pi / 36) = (-1 + 2*sin(11*pi/72)**2)*sin(pi/18) + sin(4*pi/9)*cos(4673*pi/36),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/36) = cos(4673*pi/36),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (7*pi/36) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 18) * (1 - 2 * sin(11 * pi / 72) ** 2) + sin(4 * pi / 9) * cos(7 * pi / 36) = -(1 - 2*sin(11*pi/72)**2)*sin(pi/18) + sin(4*pi/9)*cos(7*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/36) = 1 - 2 * sin(11*pi/72) ** 2,
{
have : cos(11*pi/36) = cos(2*(11*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = cos(4*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(11*pi/36) = sin(7*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw neg_mul,
rw mul_comm,
rw ← neg_mul,
have : -sin(7*pi/36)*cos(4*pi/9) + sin(4*pi/9)*cos(7*pi/36) = sin(pi/4),
{
have : sin(pi/4) = sin((4*pi/9) - (7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_four,
end


lemma Trigo_0_146_ASIB_extend(h0 : cos(x) ≠ 0) (h1 : tan(x) ≠ 0) (h2 : (sin(x+pi/2)*tan(x+pi))≠ 0) : -sin(-x + pi/2)*sin(x + 211*pi/2)*tan(-x + 3*pi)/(sin(x + pi/2)*tan(x + pi))=-(-sin(pi/2)*sin(x/2 - pi/2) + cos(pi/2)*cos(x/2 - pi/2))**2 + sin(x/2)**2:=
begin
have : sin(x / 2) ** 2 - (-sin(x / 2 - pi / 2) * sin(pi / 2) + cos(x / 2 - pi / 2) * cos(pi / 2)) ** 2 = -(-sin(pi/2)*sin(x/2 - pi/2) + cos(pi/2)*cos(x/2 - pi/2))**2 + sin(x/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(x/2) = -sin(x/2 - pi/2) * sin(pi/2) + cos(x/2 - pi/2) * cos(pi/2),
{
have : cos(x/2) = cos((x/2 - pi/2) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_rhs, rw ← this,},
have : -(-sin(x / 2) ** 2 + cos(x / 2) ** 2) = sin(x/2)**2 - cos(x/2)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(x) = -sin(x/2) ** 2 + cos(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_rhs, rw ← this,},
have : sin(-x + pi / 2) * -sin(x + 211 * pi / 2) * tan(-x + 3 * pi) / (sin(x + pi / 2) * tan(x + pi)) = -sin(-x + pi/2)*sin(x + 211*pi/2)*tan(-x + 3*pi)/(sin(x + pi/2)*tan(x + pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = -sin(x + 211*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 2*pi) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/2) = cos(x),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x + 3*pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x + 3*pi) (3),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(x + pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(x + pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_0_147_XWAG_extend(h0 : cos(pi/5) ≠ 0) (h1 : cos(2*pi/15) ≠ 0) (h2 : 1 - tan(pi/5) * tan(2*pi/15) ≠ 0)  (h3 : cos(pi/10)≠ 0) (h4 : (1-tan(pi/10)**2)≠ 0) (h5 : cos(pi/10)≠ 0) (h6 : ((-sin(pi/10)**2/cos(pi/10)**2+1)*cos(pi/10))≠ 0) (h7 : (1-(sin(pi/10)/cos(pi/10))**2)≠ 0) (h8 : sin(pi/10)≠ 0) (h9 : (2*sin(pi/10))≠ 0) (h10 : ((-4*sin(pi/10)**4/sin(pi/5)**2+1)*sin(pi/5))≠ 0) (h11 : ((-sin(pi/10)**2/(sin(pi/5)/(2*sin(pi/10)))**2+1)*(sin(pi/5)/(2*sin(pi/10))))≠ 0) (h12 : (sin(pi/5)/(2*sin(pi/10)))≠ 0) (h13 : sin(pi/5)≠ 0) : tan(2*pi/15) + 4*sqrt(3)*sin(pi/10)**2*tan(2*pi/15)/((-4*sin(pi/10)**4/sin(pi/5)**2 + 1)*sin(pi/5)) + 4*sin(pi/10)**2/((-4*sin(pi/10)**4/sin(pi/5)**2 + 1)*sin(pi/5))=sqrt(3):=
begin
have : tan(2 * pi / 15) + 2 * sqrt 3 * sin(pi / 10) * tan(2 * pi / 15) / ((-sin(pi / 10) ** 2 / (sin(pi / 5) / (2 * sin(pi / 10))) ** 2 + 1) * (sin(pi / 5) / (2 * sin(pi / 10)))) + 2 * sin(pi / 10) / ((-sin(pi / 10) ** 2 / (sin(pi / 5) / (2 * sin(pi / 10))) ** 2 + 1) * (sin(pi / 5) / (2 * sin(pi / 10)))) = tan(2*pi/15) + 4*sqrt(3)*sin(pi/10)**2*tan(2*pi/15)/((-4*sin(pi/10)**4/sin(pi/5)**2 + 1)*sin(pi/5)) + 4*sin(pi/10)**2/((-4*sin(pi/10)**4/sin(pi/5)**2 + 1)*sin(pi/5)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/10) = sin(pi/5) / ( 2 * sin(pi/10) ),
{
have : sin(pi/5) = sin(2*(pi/10)),
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
have : tan(2 * pi / 15) + 2 * sqrt 3 * (sin(pi / 10) / cos(pi / 10)) * tan(2 * pi / 15) / (1 - (sin(pi / 10) / cos(pi / 10)) ** 2) + 2 * (sin(pi / 10) / cos(pi / 10)) / (1 - (sin(pi / 10) / cos(pi / 10)) ** 2) = tan(2*pi/15) + 2*sqrt(3)*sin(pi/10)*tan(2*pi/15)/((-sin(pi/10)**2/cos(pi/10)**2 + 1)*cos(pi/10)) + 2*sin(pi/10)/((-sin(pi/10)**2/cos(pi/10)**2 + 1)*cos(pi/10)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) = sin(pi/10) / cos(pi/10),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * tan(2 * pi / 15) * (2 * tan(pi / 10) / (1 - tan(pi / 10) ** 2)) + tan(2 * pi / 15) + 2 * tan(pi / 10) / (1 - tan(pi / 10) ** 2) = tan(2*pi/15) + 2*sqrt(3)*tan(pi/10)*tan(2*pi/15)/(1 - tan(pi/10)**2) + 2*tan(pi/10)/(1 - tan(pi/10)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
rw add_assoc,
have : tan(2*pi/15) + tan(pi/5) = tan(pi/3)*(-tan(2*pi/15)*tan(pi/5) + 1),
{
rw add_comm,
rw tan_add_tan,
have : tan((pi/5) + (2*pi/15)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
have : sqrt(3)*(-tan(2*pi/15)*tan(pi/5) + 1) = -sqrt(3)*tan(2*pi/15)*tan(pi/5) + sqrt(3),
{
ring_exp,
},
rw this,
norm_num,
end


lemma Trigo_0_148_KKNW_extend(h0 : 1 - tan(pi/9) * tan(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : cos(pi/9) ≠ 0)  (h3 : cos(140*pi/3)≠ 0) (h4 : cos(pi/18)≠ 0) (h5 : tan((140*pi/3)-(pi/18))≠ 0) (h6 : 1+tan(140*pi/3)*tan(pi/18)≠ 0) (h7 : tan(839*pi/18)≠ 0) : (tan(pi/18) - tan(389*pi/3))/tan(839*pi/18) + tan(pi/18)*tan(pi/9) - tan(pi/9)*tan(389*pi/3) + 1=1:=
begin
have : -(tan(389 * pi / 3) - tan(pi / 18)) / tan(839 * pi / 18) + tan(pi / 18) * tan(pi / 9) - tan(pi / 9) * tan(389 * pi / 3) + 1 = (tan(pi/18) - tan(389*pi/3))/tan(839*pi/18) + tan(pi/18)*tan(pi/9) - tan(pi/9)*tan(389*pi/3) + 1,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(140*pi/3) = tan(389*pi/3),
{
rw tan_eq_tan_add_int_mul_pi (140*pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi / 18) * tan(pi / 9) - ((tan(140 * pi / 3) - tan(pi / 18)) / tan(839 * pi / 18) - 1) - tan(pi / 9) * tan(140 * pi / 3) = -(tan(140*pi/3) - tan(pi/18))/tan(839*pi/18) + tan(pi/18)*tan(pi/9) - tan(pi/9)*tan(140*pi/3) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(140*pi/3) * tan(pi/18) = ( tan(140*pi/3) - tan(pi/18) ) / tan(839*pi/18) - 1,
{
rw tan_mul_tan,
have : tan((140*pi/3) - (pi/18)) = tan(839*pi/18),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(140*pi/3) * tan(pi/18)) = tan(pi/18)*tan(140*pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : tan(pi / 18) * tan(pi / 9) + tan(pi / 18) * -tan(140 * pi / 3) + tan(pi / 9) * -tan(140 * pi / 3) = tan(pi/18)*tan(pi/9) - tan(pi/18)*tan(140*pi/3) - tan(pi/9)*tan(140*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = -tan(140*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_pi_div_three,
rw add_assoc,
have : tan(pi/18)*sqrt(3) + tan(pi/9)*sqrt(3) = sqrt(3)*(tan(pi/18) + tan(pi/9)),
{
ring_exp,
},
rw this,
have : tan(pi/18) + tan(pi/9) = (-tan(pi/18)*tan(pi/9) + 1)*tan(pi/6),
{
rw add_comm,
rw tan_add_tan,
have : tan((pi/9) + (pi/18)) = tan(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_six,
ring_exp,
rw sq_sqrt,
norm_num,
repeat {linarith},
end


lemma Trigo_0_149_DXJL_extend : (cos(pi/2)*cos(20*pi/9) + sin(pi/2)*sin(20*pi/9))*sin(1781*pi/9) + sin(5*pi/18)*sin(227*pi/18)=1/2:=
begin
have : sin(1781 * pi / 9) * (sin(20 * pi / 9) * sin(pi / 2) + cos(20 * pi / 9) * cos(pi / 2)) + sin(5 * pi / 18) * sin(227 * pi / 18) = (cos(pi/2)*cos(20*pi/9) + sin(pi/2)*sin(20*pi/9))*sin(1781*pi/9) + sin(5*pi/18)*sin(227*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(31*pi/18) = sin(20*pi/9) * sin(pi/2) + cos(20*pi/9) * cos(pi/2),
{
have : cos(31*pi/18) = cos((20*pi/9) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = sin(227*pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/18) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 18) * sin(7 * pi / 18) + sin(1781 * pi / 9) * cos(31 * pi / 18) = sin(1781*pi/9)*cos(31*pi/18) + sin(5*pi/18)*sin(7*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/18) = sin(1781*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/18) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/18) = -cos(7*pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (11*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(31*pi/18) = cos(5*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (31*pi/18) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw neg_mul,
rw mul_comm,
rw ← neg_mul,
have : -cos(5*pi/18)*cos(7*pi/18) + sin(5*pi/18)*sin(7*pi/18) = -cos(2*pi/3),
{
have : cos(2*pi/3) = -sin(5*pi/18)*sin(7*pi/18) + cos(5*pi/18)*cos(7*pi/18),
{
have : cos(2*pi/3) = cos((5*pi/18) + (7*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
rw cos_two_pi_div_three,
norm_num,
end


lemma Trigo_1_150_YLPG_extend : 2*(-1 + 2*(-sin(299*pi/12)**2 + cos(299*pi/12)**2)**2)**2 + sqrt(3)*sin(2*pi/3)=2:=
begin
have : 2 * (-1 + 2 * (-sin(299 * pi / 12) ** 2 + cos(299 * pi / 12) ** 2) ** 2) ** 2 + sqrt 3 * sin(2 * pi / 3) = 2*(-1 + 2*(-sin(299*pi/12)**2 + cos(299*pi/12)**2)**2)**2 + sqrt(3)*sin(2*pi/3),
{
field_simp at *,
},
have : cos(299*pi/6) = -sin(299*pi/12) ** 2 + cos(299*pi/12) ** 2,
{
have : cos(299*pi/6) = cos(2*(299*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (2 * cos(299 * pi / 6) ** 2 - 1) ** 2 + sqrt 3 * sin(2 * pi / 3) = 2*(-1 + 2*cos(299*pi/6)**2)**2 + sqrt(3)*sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(299*pi/3) = 2 * cos(299*pi/6) ** 2 - 1,
{
have : cos(299*pi/3) = cos(2*(299*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(2 * pi / 3) + 2 * cos(299 * pi / 3) ** 2 = 2*cos(299*pi/3)**2 + sqrt(3)*sin(2*pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = cos(299*pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/3) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw cos_pi_div_three,
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
norm_num,
ring_exp,
rw sq_sqrt,
norm_num,
repeat {linarith},
end


lemma Trigo_1_151_EOYC_extend(h0 : cos(pi/3) ≠ 0) (h1 : 1 + tan(pi/3) * tan(pi/18) ≠ 0) (h2 : cos(pi/18) ≠ 0) (h3: sin(2*pi/9) ≠ 0)  : (-sin(-2*pi)*cos(-16*pi/9) + cos(-2*pi)*cos(3343*pi/18))*(-tan(1351*pi/18) + sqrt(3))=1:=
begin
have : (-sin((-2) * pi) * cos((-16) * pi / 9) + cos((-2) * pi) * cos(3343 * pi / 18)) * (-tan(1351 * pi / 18) + sqrt 3) = (-sin(-2*pi)*cos(-16*pi/9) + cos(-2*pi)*cos(3343*pi/18))*(-tan(1351*pi/18) + sqrt(3)),
{
field_simp at *,
},
have : tan(pi/18) = tan(1351*pi/18),
{
rw tan_eq_tan_add_int_mul_pi (pi/18) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin((-2) * pi) * cos((-16) * pi / 9) + cos(3343 * pi / 18) * cos((-2) * pi)) * (-tan(pi / 18) + sqrt 3) = (-sin(-2*pi)*cos(-16*pi/9) + cos(-2*pi)*cos(3343*pi/18))*(-tan(pi/18) + sqrt(3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-16*pi/9) = cos(3343*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-16*pi/9) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-tan(pi / 18) + sqrt 3) * (sin((-16) * pi / 9) * cos((-2) * pi) - sin((-2) * pi) * cos((-16) * pi / 9)) = (-sin(-2*pi)*cos(-16*pi/9) + sin(-16*pi/9)*cos(-2*pi))*(-tan(pi/18) + sqrt(3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = sin(-16*pi/9) * cos(-2*pi) - sin(-2*pi) * cos(-16*pi/9),
{
have : sin(2*pi/9) = sin((-16*pi/9) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
rw ← tan_pi_div_three,
have : -tan(pi/18) + tan(pi/3) = (tan(pi/18)*tan(pi/3) + 1)*tan(5*pi/18),
{
rw neg_add_eq_sub,
rw tan_sub_tan,
have : tan((pi/3) - (pi/18)) = tan(5*pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
repeat {rw tan_eq_sin_div_cos},
have : cos(5*pi/18) = sin(2*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
have : sin(pi / 18) / cos(pi / 18) * (sin(pi / 3) / (1 / 2)) = 2*sin(pi/18)*sin(pi/3)/cos(pi/18),
{
field_simp,
ring_exp,
},
rw this,
have : 2*sin(pi/18)*sin(pi/3)/cos(pi/18) + 1 = (2*sin(pi/18)*sin(pi/3) + cos(pi/18))/cos(pi/18),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three],
},
rw this,
have : cos(pi/18) = 2*cos(pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : 2*sin(pi/18)*sin(pi/3) + 2*cos(pi/18)*cos(pi/3) = 2*cos(5*pi/18),
{
have : cos(5*pi/18) = sin(pi/18)*sin(pi/3) + cos(pi/18)*cos(pi/3),
{
have : cos(5*pi/18) = cos((pi/3) - (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
linarith,
},
rw this,
rw cos_pi_div_three,
field_simp,
left,
have : 2*cos(5*pi/18)*2*sin(5*pi/18) = 4*sin(5*pi/18)*cos(5*pi/18),
{
ring,
},
rw this,
have : 4*sin(5*pi/18)*cos(5*pi/18) = 2*sin(5*pi/9),
{
have : sin(5*pi/9) = sin(2*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
ring,
},
rw this,
have : sin(5*pi/9) = cos(pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
end


lemma Trigo_1_152_LXYX_extend(h0 : cos(x)**2 ≠ 0)  (h1 : sin(-x+273*pi/2)≠ 0) : -(-4*cos(x/3 + 187*pi/2)**3 + 3*cos(x/3 + 187*pi/2))**5/sin(-x + 273*pi/2)**2 + (-4*cos(x/3 + 187*pi/2)**3 + 3*cos(x/3 + 187*pi/2))*sin(-x + 273*pi/2)**2 + (-4*cos(x/3 + 187*pi/2)**3 + 3*cos(x/3 + 187*pi/2))/sin(-x + 273*pi/2)**2 + 8*cos(x/3 + 187*pi/2)**3 - 6*cos(x/3 + 187*pi/2)=0:=
begin
have : -((-4) * cos(x / 3 + 187 * pi / 2) ** 3 + 3 * cos(x / 3 + 187 * pi / 2)) ** 5 / sin(-x + 273 * pi / 2) ** 2 + ((-4) * cos(x / 3 + 187 * pi / 2) ** 3 + 3 * cos(x / 3 + 187 * pi / 2)) * sin(-x + 273 * pi / 2) ** 2 + ((-4) * cos(x / 3 + 187 * pi / 2) ** 3 + 3 * cos(x / 3 + 187 * pi / 2)) / sin(-x + 273 * pi / 2) ** 2 + 8 * cos(x / 3 + 187 * pi / 2) ** 3 - 6 * cos(x / 3 + 187 * pi / 2) = -(-4*cos(x/3 + 187*pi/2)**3 + 3*cos(x/3 + 187*pi/2))**5/sin(-x + 273*pi/2)**2 + (-4*cos(x/3 + 187*pi/2)**3 + 3*cos(x/3 + 187*pi/2))*sin(-x + 273*pi/2)**2 + (-4*cos(x/3 + 187*pi/2)**3 + 3*cos(x/3 + 187*pi/2))/sin(-x + 273*pi/2)**2 + 8*cos(x/3 + 187*pi/2)**3 - 6*cos(x/3 + 187*pi/2),
{
field_simp at *,
},
have : sin(x/3) = cos(x/3 + 187*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x/3) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -((-4) * sin(x / 3) ** 3 + 3 * sin(x / 3)) ** 5 / sin(-x + 273 * pi / 2) ** 2 + ((-4) * sin(x / 3) ** 3 + 3 * sin(x / 3)) * sin(-x + 273 * pi / 2) ** 2 - 2 * ((-4) * sin(x / 3) ** 3 + 3 * sin(x / 3)) + ((-4) * sin(x / 3) ** 3 + 3 * sin(x / 3)) / sin(-x + 273 * pi / 2) ** 2 = -(-4*sin(x/3)**3 + 3*sin(x/3))**5/sin(-x + 273*pi/2)**2 + (-4*sin(x/3)**3 + 3*sin(x/3))*sin(-x + 273*pi/2)**2 + (-4*sin(x/3)**3 + 3*sin(x/3))/sin(-x + 273*pi/2)**2 + 8*sin(x/3)**3 - 6*sin(x/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -4 * sin(x/3) ** 3 + 3 * sin(x/3),
{
have : sin(x) = sin(3*(x/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) * sin(-x + 273 * pi / 2) ** 2 - 2 * sin(x) + sin(x) / sin(-x + 273 * pi / 2) ** 2 - sin(x) ** 5 / sin(-x + 273 * pi / 2) ** 2 = -sin(x)**5/sin(-x + 273*pi/2)**2 + sin(x)*sin(-x + 273*pi/2)**2 - 2*sin(x) + sin(x)/sin(-x + 273*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(-x + 273*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (x) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x)*cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2 - sin(x)**5/cos(x)**2 = -sin(x)**5/cos(x)**2 + sin(x)*cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2,
{
ring,
},
rw this,
have : -sin(x)**5/cos(x)**2 + sin(x)*cos(x)**2 = (-sin(x)**5 + sin(x)*cos(x)**4)/cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : -sin(x)**5 + sin(x)*cos(x)**4 = (-sin(x)**4 + cos(x)**4)*sin(x),
{
ring_exp,
},
rw this,
have : -sin(x)**4 + cos(x)**4 = (-sin(x)**2 + cos(x)**2)*(sin(x)**2 + cos(x)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
simp,
have : (-sin(x)**2 + cos(x)**2)*sin(x)/cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2 = ((-sin(x)**2 + cos(x)**2)*sin(x) - 2*sin(x)*cos(x)**2 + sin(x))/cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : (-sin(x)**2 + cos(x)**2)*sin(x) = -sin(x)**3 + sin(x)*cos(x)**2,
{
ring_exp,
},
rw this,
have : -sin(x)**3 = sin(x)*cos(x)**2 -sin(x)*(sin(x)**2 + cos(x)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
left,
ring_exp,
end


lemma Trigo_1_153_IKXK_extend(h0 : cos(67*pi/180) ≠ 0) (h1 : cos(17*pi/45) ≠ 0) (h2 : 1 - tan(17*pi/45) * tan(67*pi/180) ≠ 0)  (h3 : tan(2981*pi/90)≠ 0) (h4 : cos(3071*pi/90)≠ 0) (h5 : cos(pi)≠ 0) (h6 : (-tan(pi)+tan(3071*pi/90))≠ 0) (h7 : ((tan(3071*pi/90)-tan(pi))/(1+tan(3071*pi/90)*tan(pi)))≠ 0) (h8 : (1+tan(3071*pi/90)*tan(pi))≠ 0) (h9 : cos((2*pi)/2)≠ 0) (h10 : sin(2*pi)≠ 0) (h11 : (-(1-cos(2*pi))/sin(2*pi)+tan(3071*pi/90))≠ 0) (h12 : (-((1-cos(2*pi))/sin(2*pi))+tan(3071*pi/90))≠ 0) : (-(1 - cos(2*pi))*tan(3071*pi/90)/sin(2*pi) - 1)*tan(67*pi/180)/(-(1 - cos(2*pi))/sin(2*pi) + tan(3071*pi/90)) + tan(67*pi/180) + (1 + (1 - cos(2*pi))*tan(3071*pi/90)/sin(2*pi))/(-(1 - cos(2*pi))/sin(2*pi) + tan(3071*pi/90))=-1:=
begin
have : -((1 - cos(2 * pi)) / sin(2 * pi) * tan(3071 * pi / 90) + 1) * tan(67 * pi / 180) / (-((1 - cos(2 * pi)) / sin(2 * pi)) + tan(3071 * pi / 90)) + tan(67 * pi / 180) + ((1 - cos(2 * pi)) / sin(2 * pi) * tan(3071 * pi / 90) + 1) / (-((1 - cos(2 * pi)) / sin(2 * pi)) + tan(3071 * pi / 90)) = (-(1 - cos(2*pi))*tan(3071*pi/90)/sin(2*pi) - 1)*tan(67*pi/180)/(-(1 - cos(2*pi))/sin(2*pi) + tan(3071*pi/90)) + tan(67*pi/180) + (1 + (1 - cos(2*pi))*tan(3071*pi/90)/sin(2*pi))/(-(1 - cos(2*pi))/sin(2*pi) + tan(3071*pi/90)),
{
field_simp at *,
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
have : -tan(67 * pi / 180) / ((tan(3071 * pi / 90) - tan(pi)) / (1 + tan(3071 * pi / 90) * tan(pi))) + tan(67 * pi / 180) + 1 / ((tan(3071 * pi / 90) - tan(pi)) / (1 + tan(3071 * pi / 90) * tan(pi))) = -(tan(pi)*tan(3071*pi/90) + 1)*tan(67*pi/180)/(-tan(pi) + tan(3071*pi/90)) + tan(67*pi/180) + (tan(pi)*tan(3071*pi/90) + 1)/(-tan(pi) + tan(3071*pi/90)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(2981*pi/90) = ( tan(3071*pi/90) - tan(pi) ) / ( 1 + tan(3071*pi/90) * tan(pi) ),
{
have : tan(2981*pi/90) = tan((3071*pi/90) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -tan(67 * pi / 180) * (1 / tan(2981 * pi / 90)) + tan(67 * pi / 180) + 1 / tan(2981 * pi / 90) = -tan(67*pi/180)/tan(2981*pi/90) + tan(67*pi/180) + 1/tan(2981*pi/90),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(17*pi/45) = 1 / tan(2981*pi/90),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (17*pi/45) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(67*pi/180) + tan(17*pi/45) = (-tan(67*pi/180)*tan(17*pi/45) + 1)*tan(3*pi/4),
{
rw add_comm,
rw tan_add_tan,
have : tan((17*pi/45) + (67*pi/180)) = tan(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_three_pi_div_four,
norm_num,
end


lemma Trigo_1_154_XUWJ_extend(h0 : cos(pi/6) ≠ 0) (h1 : 1 - tan(pi/6) * tan(pi/12) ≠ 0) (h2 : cos(pi/12) ≠ 0)  (h3 : cos(13*pi/6)≠ 0) (h4 : cos(2*pi)≠ 0) (h5 : (tan(2*pi)*tan(13*pi/6)+1)≠ 0) (h6 : (1+tan(13*pi/6)*tan(2*pi))≠ 0) (h7 : (tan(3*pi)*tan(13*pi/6)+1)≠ 0) (h8 : (tan(13*pi/6)*tan(3*pi)+1)≠ 0) (h9 : cos((6*pi)/2)≠ 0) (h10 : sin(6*pi)≠ 0) (h11 : (tan(13*pi/6)*((1-cos(6*pi))/sin(6*pi))+1)≠ 0) (h12 : (1+(1-cos(6*pi))*tan(13*pi/6)/sin(6*pi))≠ 0) : (-(1 - cos(6*pi))/sin(6*pi) + tan(13*pi/6))*tan(pi/12)/(1 + (1 - cos(6*pi))*tan(13*pi/6)/sin(6*pi)) + tan(pi/12) + (-(1 - cos(6*pi))/sin(6*pi) + tan(13*pi/6))/(1 + (1 - cos(6*pi))*tan(13*pi/6)/sin(6*pi))=1:=
begin
have : (-((1 - cos(6 * pi)) / sin(6 * pi)) + tan(13 * pi / 6)) * tan(pi / 12) / (tan(13 * pi / 6) * ((1 - cos(6 * pi)) / sin(6 * pi)) + 1) + tan(pi / 12) + (-((1 - cos(6 * pi)) / sin(6 * pi)) + tan(13 * pi / 6)) / (tan(13 * pi / 6) * ((1 - cos(6 * pi)) / sin(6 * pi)) + 1) = (-(1 - cos(6*pi))/sin(6*pi) + tan(13*pi/6))*tan(pi/12)/(1 + (1 - cos(6*pi))*tan(13*pi/6)/sin(6*pi)) + tan(pi/12) + (-(1 - cos(6*pi))/sin(6*pi) + tan(13*pi/6))/(1 + (1 - cos(6*pi))*tan(13*pi/6)/sin(6*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi) = ( 1 - cos(6*pi) ) / sin(6*pi),
{
have : tan(3*pi) = tan((6*pi)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-tan(3 * pi) + tan(13 * pi / 6)) * tan(pi / 12) / (tan(3 * pi) * tan(13 * pi / 6) + 1) + tan(pi / 12) + (-tan(3 * pi) + tan(13 * pi / 6)) / (tan(3 * pi) * tan(13 * pi / 6) + 1) = (-tan(3*pi) + tan(13*pi/6))*tan(pi/12)/(tan(13*pi/6)*tan(3*pi) + 1) + tan(pi/12) + (-tan(3*pi) + tan(13*pi/6))/(tan(13*pi/6)*tan(3*pi) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi) = tan(3*pi),
{
rw tan_eq_tan_add_int_mul_pi (2*pi) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi / 12) * ((tan(13 * pi / 6) - tan(2 * pi)) / (1 + tan(13 * pi / 6) * tan(2 * pi))) + tan(pi / 12) + (tan(13 * pi / 6) - tan(2 * pi)) / (1 + tan(13 * pi / 6) * tan(2 * pi)) = (-tan(2*pi) + tan(13*pi/6))*tan(pi/12)/(tan(2*pi)*tan(13*pi/6) + 1) + tan(pi/12) + (-tan(2*pi) + tan(13*pi/6))/(tan(2*pi)*tan(13*pi/6) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/6) = ( tan(13*pi/6) - tan(2*pi) ) / ( 1 + tan(13*pi/6) * tan(2*pi) ),
{
have : tan(pi/6) = tan((13*pi/6) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(pi/12) + tan(pi/6) = (-tan(pi/12)*tan(pi/6) + 1)*tan(pi/4),
{
rw add_comm,
rw tan_add_tan,
have : tan((pi/6) + (pi/12)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_1_155_TOUL_extend(h0 : cos(29*pi/180) ≠ 0) (h1 : cos(29*pi/180)≠ 0) : (-cos(55*pi/6)*cos(16679*pi/180) + sin(59*pi/180))/cos(29*pi/180)=1/2:=
begin
have : sin(34*pi/3) = cos(55*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (34*pi/3) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(16679 * pi / 180) * sin(34 * pi / 3) + sin(59 * pi / 180)) / cos(29 * pi / 180) = (-sin(34*pi/3)*cos(16679*pi/180) + sin(59*pi/180))/cos(29*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(29*pi/180) = -cos(16679*pi/180),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (29*pi/180) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(29 * pi / 180) * -sin(34 * pi / 3) + sin(59 * pi / 180)) / cos(29 * pi / 180) = (sin(29*pi/180)*sin(34*pi/3) + sin(59*pi/180))/cos(29*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(34*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(59*pi/180) = sin(29*pi/180)*cos(pi/6) + sin(pi/6)*cos(29*pi/180),
{
have : sin(59*pi/180) = sin((pi/6) + (29*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_156_EDMO_extend(h0 : cos(2*pi/9) ≠ 0) (h1 : 1 - tan(pi/9) * tan(2*pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0) (h3 : tan(pi/9) ≠ 0) (h4 : tan(2*pi/9) ≠ 0)  (h5 : cos((4*pi/9)/2)≠ 0) (h6 : sin(4*pi/9)≠ 0) (h7 : (tan(pi/9)*((1-cos(4*pi/9))/sin(4*pi/9)))≠ 0) (h8 : ((1-cos(4*pi/9))*tan(pi/9))≠ 0) (h9 : -cos(3149*pi/18)≠ 0) (h10 : cos(3149*pi/18)≠ 0) (h11 : ((1- -cos(707*pi/9))*tan(pi/9))≠ 0) (h12 : ((cos(707*pi/9)+1)*tan(pi/9))≠ 0) : ((cos(707*pi/9) + 1)/cos(3149*pi/18) - tan(pi/9) - tan(2*pi/3))*cos(3149*pi/18)/((cos(707*pi/9) + 1)*tan(pi/9))=-sqrt(3):=
begin
have : -(tan(2 * pi / 3) + tan(pi / 9) - (1 - -cos(707 * pi / 9)) / cos(3149 * pi / 18)) * cos(3149 * pi / 18) / ((1 - -cos(707 * pi / 9)) * tan(pi / 9)) = ((cos(707*pi/9) + 1)/cos(3149*pi/18) - tan(pi/9) - tan(2*pi/3))*cos(3149*pi/18)/((cos(707*pi/9) + 1)*tan(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = -cos(707*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (4*pi/9) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(2 * pi / 3) + tan(pi / 9) + (1 - cos(4 * pi / 9)) / -cos(3149 * pi / 18)) * -cos(3149 * pi / 18) / ((1 - cos(4 * pi / 9)) * tan(pi / 9)) = -(tan(2*pi/3) + tan(pi/9) - (1 - cos(4*pi/9))/cos(3149*pi/18))*cos(3149*pi/18)/((1 - cos(4*pi/9))*tan(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = -cos(3149*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 9) + (1 - cos(4 * pi / 9)) / sin(4 * pi / 9) + tan(2 * pi / 3)) / (tan(pi / 9) * ((1 - cos(4 * pi / 9)) / sin(4 * pi / 9))) = (tan(2*pi/3) + tan(pi/9) + (1 - cos(4*pi/9))/sin(4*pi/9))*sin(4*pi/9)/((1 - cos(4*pi/9))*tan(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/9) = ( 1 - cos(4*pi/9) ) / sin(4*pi/9),
{
have : tan(2*pi/9) = tan((4*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) + tan(2*pi/9) = (-tan(pi/9)*tan(2*pi/9) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/9) + (2*pi/9)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
rw tan_two_pi_div_three,
have : (-tan(pi/9)*tan(2*pi/9) + 1)*sqrt(3) = -sqrt(3)*tan(pi/9)*tan(2*pi/9) + sqrt(3),
{
ring_exp,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_157_ZCQS_extend(h0 : cos(2*pi/9) ≠ 0) (h1 : 1 - tan(pi/9) * tan(2*pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0)  (h3 : cos(pi/9)≠ 0) (h4 : cos(2*pi/9)≠ 0) (h5 : 1 - tan(pi/9) * tan(2*pi/9)≠ 0) (h6 : cos((4*pi/9)/2)≠ 0) (h7 : (1+cos(4*pi/9))≠ 0) (h8 : (cos(4*pi/9)+1)≠ 0) (h9 : cos((2*pi/9)/2)≠ 0) (h10 : (1+cos(2*pi/9))≠ 0) (h11 : ((cos(2*pi/9)+1)*(cos(4*pi/9)+1))≠ 0) : sqrt(3)*sin(2*pi/9)*sin(4*pi/9)/((cos(2*pi/9) + 1)*(cos(4*pi/9) + 1)) + (-sin(2*pi/9)*sin(4*pi/9)/((cos(2*pi/9) + 1)*(cos(4*pi/9) + 1)) + 1)*tan(pi/3)=sqrt(3):=
begin
have : sqrt 3 * sin(4 * pi / 9) * (sin(2 * pi / 9) / (1 + cos(2 * pi / 9))) / (cos(4 * pi / 9) + 1) + (-sin(4 * pi / 9) * (sin(2 * pi / 9) / (1 + cos(2 * pi / 9))) / (cos(4 * pi / 9) + 1) + 1) * tan(pi / 3) = sqrt(3)*sin(2*pi/9)*sin(4*pi/9)/((cos(2*pi/9) + 1)*(cos(4*pi/9) + 1)) + (-sin(2*pi/9)*sin(4*pi/9)/((cos(2*pi/9) + 1)*(cos(4*pi/9) + 1)) + 1)*tan(pi/3),
{
field_simp at *,
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
have : sqrt 3 * tan(pi / 9) * (sin(4 * pi / 9) / (1 + cos(4 * pi / 9))) + (-tan(pi / 9) * (sin(4 * pi / 9) / (1 + cos(4 * pi / 9))) + 1) * tan(pi / 3) = sqrt(3)*sin(4*pi/9)*tan(pi/9)/(cos(4*pi/9) + 1) + (-sin(4*pi/9)*tan(pi/9)/(cos(4*pi/9) + 1) + 1)*tan(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/9) = sin(4*pi/9) / ( 1 + cos(4*pi/9) ),
{
have : tan(2*pi/9) = tan((4*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-tan(pi / 9) * tan(2 * pi / 9) + 1) * tan(pi / 3) + sqrt 3 * tan(pi / 9) * tan(2 * pi / 9) = sqrt(3)*tan(pi/9)*tan(2*pi/9) + (-tan(pi/9)*tan(2*pi/9) + 1)*tan(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) + tan(2*pi/9) = ( -tan(pi/9) * tan(2*pi/9) + 1 ) * tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/9) + (2*pi/9)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(pi/9) + tan(2*pi/9)) + sqrt(3)*tan(pi/9)*tan(2*pi/9) = sqrt(3)*tan(pi/9)*tan(2*pi/9)+tan(pi/9)+tan(2*pi/9),
{
ring,
},
conv {to_lhs, rw this,},
rw add_assoc,
have : tan(pi/9) + tan(2*pi/9) = (-tan(pi/9)*tan(2*pi/9) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/9) + (2*pi/9)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
have : (-tan(pi/9)*tan(2*pi/9) + 1)*sqrt(3) = -sqrt(3)*tan(pi/9)*tan(2*pi/9) + sqrt(3),
{
ring_exp,
},
rw this,
norm_num,
end


lemma Trigo_1_158_WJWZ_extend(h0 : sin(8*pi/9) ≠ 0) (h1 : sin(pi/9) ≠ 0) : (-sin(2*pi)*cos(2735*pi/18) - sin(2735*pi/18)*sin(389*pi/2))*cos(pi/9)*cos(2*pi/9)*cos(pi/3)=1/16:=
begin
have : -(sin(2735 * pi / 18) * sin(389 * pi / 2) + sin(2 * pi) * cos(2735 * pi / 18)) * cos(pi / 9) * cos(2 * pi / 9) * cos(pi / 3) = (-sin(2*pi)*cos(2735*pi/18) - sin(2735*pi/18)*sin(389*pi/2))*cos(pi/9)*cos(2*pi/9)*cos(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi) = sin(389*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*pi) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2771*pi/18) = sin(2735*pi/18) * cos(2*pi) + sin(2*pi) * cos(2735*pi/18),
{
have : sin(2771*pi/18) = sin((2735*pi/18) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 9) * cos(2 * pi / 9) * cos(pi / 3) * -sin(2771 * pi / 18) = -sin(2771*pi/18)*cos(pi/9)*cos(2*pi/9)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = -sin(2771*pi/18),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/9) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
rw div_mul_eq_mul_div,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/9)/2/(2*sin(pi/9))*cos(pi/3)*cos(4*pi/9) = sin(4*pi/ 9)*cos(4*pi/9)/2/(2*sin(pi/9))*cos(pi/3),
{
ring,
},
rw this,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(pi/9) = sin(8*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_1_159_TUMT_extend(h0: cos(17*pi/180) ≠ 0) (h1 : cos(17*pi/180)≠ 0) : (-cos(4213*pi/180)*cos(1097*pi/6) - 4*sin(47*pi/540)**3 + 3*sin(47*pi/540))/cos(17*pi/180)=1/2:=
begin
have : (-cos(4213 * pi / 180) * cos(1097 * pi / 6) + ((-4) * sin(47 * pi / 540) ** 3 + 3 * sin(47 * pi / 540))) / cos(17 * pi / 180) = (-cos(4213*pi/180)*cos(1097*pi/6) - 4*sin(47*pi/540)**3 + 3*sin(47*pi/540))/cos(17*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(47*pi/180) = -4 * sin(47*pi/540) ** 3 + 3 * sin(47*pi/540),
{
have : sin(47*pi/180) = sin(3*(47*pi/540)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(1097 * pi / 6) * cos(4213 * pi / 180) + sin(47 * pi / 180)) / cos(17 * pi / 180) = (-cos(4213*pi/180)*cos(1097*pi/6) + sin(47*pi/180))/cos(17*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -cos(1097*pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/6) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (- -cos(4213 * pi / 180) * cos(pi / 6) + sin(47 * pi / 180)) / cos(17 * pi / 180) = (cos(pi/6)*cos(4213*pi/180) + sin(47*pi/180))/cos(17*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/180) = -cos(4213*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (17*pi/180) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(47*pi/180) = sin(17*pi/180)*cos(pi/6) + sin(pi/6)*cos(17*pi/180),
{
have : sin(47*pi/180) = sin((pi/6) + (17*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_160_BMST_extend : ((-sin(-pi/4)**2 + cos(-pi/4)**2)*sin(-73*pi/180) + sin(17*pi/180)/2 - sin(-163*pi/180)/2)*cos(227*pi/180) + sin(47*pi/180)*sin(73*pi/180)=1/2:=
begin
have : (sin((-73) * pi / 180) * (-sin(-pi / 4) ** 2 + cos(-pi / 4) ** 2) + sin(17 * pi / 180) / 2 - sin((-163) * pi / 180) / 2) * cos(227 * pi / 180) + sin(47 * pi / 180) * sin(73 * pi / 180) = ((-sin(-pi/4)**2 + cos(-pi/4)**2)*sin(-73*pi/180) + sin(17*pi/180)/2 - sin(-163*pi/180)/2)*cos(227*pi/180) + sin(47*pi/180)*sin(73*pi/180),
{
field_simp at *,
repeat {left},
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
have : (sin((-73) * pi / 180) * cos(-pi / 2) - (-sin(17 * pi / 180) / 2 + sin((-163) * pi / 180) / 2)) * cos(227 * pi / 180) + sin(47 * pi / 180) * sin(73 * pi / 180) = (sin(-73*pi/180)*cos(-pi/2) + sin(17*pi/180)/2 - sin(-163*pi/180)/2)*cos(227*pi/180) + sin(47*pi/180)*sin(73*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/2) * cos(-73*pi/180) = -sin(17*pi/180) / 2 + sin(-163*pi/180) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-73*pi/180) + (-pi/2)) = sin(-163*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-73*pi/180) - (-pi/2)) = sin(17*pi/180),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi/2) * cos(-73*pi/180)) = sin(-pi/2)*cos(-73*pi/180),
{
ring,
},
have : (sin((-73) * pi / 180) * cos(-pi / 2) - sin(-pi / 2) * cos((-73) * pi / 180)) * cos(227 * pi / 180) + sin(47 * pi / 180) * sin(73 * pi / 180) = (sin(-73*pi/180)*cos(-pi/2) - sin(-pi/2)*cos(-73*pi/180))*cos(227*pi/180) + sin(47*pi/180)*sin(73*pi/180),
{
field_simp at *,
},
have : sin(17*pi/180) = sin(-73*pi/180) * cos(-pi/2) - sin(-pi/2) * cos(-73*pi/180),
{
have : sin(17*pi/180) = sin((-73*pi/180) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(227*pi/180) = -cos(47*pi/180),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (227*pi/180) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(17*pi/180) = cos(73*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (17*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_neg,
rw mul_comm,
rw ← neg_mul,
have : -cos(47*pi/180)*cos(73*pi/180) + sin(47*pi/180)*sin(73*pi/180) = -cos(2*pi/3),
{
have : cos(2*pi/3) = -sin(47*pi/180)*sin(73*pi/180) + cos(47*pi/180)*cos(73*pi/180),
{
have : cos(2*pi/3) = cos((47*pi/180) + (73*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
rw cos_two_pi_div_three,
norm_num,
end


lemma Trigo_1_161_JYRW_extend(h0 : sin(4) ≤ 0) : sqrt(1 - (-sin(2)**2 + (cos(2*pi)*cos(2 + 176*pi) + sin(2*pi)*sin(2 + 2*pi))**2)**2)=-sin(4):=
begin
have : cos(2 + 2*pi) = cos(2 + 176*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2 + 2*pi) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (1 - (-sin(2) ** 2 + (sin(2 + 2 * pi) * sin(2 * pi) + cos(2 + 2 * pi) * cos(2 * pi)) ** 2) ** 2) = sqrt(1 - (-sin(2)**2 + (cos(2*pi)*cos(2 + 2*pi) + sin(2*pi)*sin(2 + 2*pi))**2)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2) = sin(2 + 2*pi) * sin(2*pi) + cos(2 + 2*pi) * cos(2*pi),
{
have : cos(2) = cos((2 + 2*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4) = -sin(2) ** 2 + cos(2) ** 2,
{
have : cos(4) = cos(2*(2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
rw cos_sq',
norm_num,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h0,
end


lemma Trigo_1_162_RSPH_extend : sin(71*pi/18) + sin(2*pi/3) + (-8*sin(7*pi/108)**3 + 6*sin(7*pi/108))*cos(5*pi/36)=sqrt(3):=
begin
have : sin(71 * pi / 18) + sin(2 * pi / 3) + 2 * ((-4) * sin(7 * pi / 108) ** 3 + 3 * sin(7 * pi / 108)) * cos(5 * pi / 36) = sin(71*pi/18) + sin(2*pi/3) + (-8*sin(7*pi/108)**3 + 6*sin(7*pi/108))*cos(5*pi/36),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/18) = sin(71*pi/18),
{
rw sin_eq_sin_add_int_mul_two_pi (-pi/18) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 18) + sin(2 * pi / 3) + 2 * ((-4) * sin(7 * pi / 108) ** 3 + 3 * sin(7 * pi / 108)) * cos(5 * pi / 36) = sin(-pi/18) + sin(2*pi/3) + 2*(-4*sin(7*pi/108)**3 + 3*sin(7*pi/108))*cos(5*pi/36),
{
field_simp at *,
},
have : sin(7*pi/36) = -4 * sin(7*pi/108) ** 3 + 3 * sin(7*pi/108),
{
have : sin(7*pi/36) = sin(3*(7*pi/108)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(7 * pi / 36) * cos(5 * pi / 36) + 2 * (sin(-pi / 18) / 2 + sin(2 * pi / 3) / 2) = sin(-pi/18) + sin(2*pi/3) + 2*sin(7*pi/36)*cos(5*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/36) * cos(13*pi/36) = sin(-pi/18) / 2 + sin(2*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((11*pi/36) + (13*pi/36)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((11*pi/36) - (13*pi/36)) = sin(-pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 2*(sin(11*pi/36) * cos(13*pi/36)) = 2*sin(11*pi/36)*cos(13*pi/36),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(7*pi/36) = cos(11*pi/36),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(11*pi/36) = sin(7*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(11*pi/36) = cos(7*pi/36),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(13*pi/36) = sin(5*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_right_comm,
have : 2*sin(5*pi/36)*cos(7*pi/36) + 2*sin(7*pi/36)*cos(5*pi/36) = 2*sin(pi/3),
{
have : sin(pi/3) = sin(5*pi/36)*cos(7*pi/36) + sin(7*pi/36)*cos(5*pi/36),
{
have : sin(pi/3) = sin((5*pi/36) + (7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
rw sin_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_1_163_YAML_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (sin(x+2*pi)*cos(pi-x)*(1/tan(-x+145*pi/2)))≠ 0) (h3 : (sin(x+2*pi)*cos(pi-x))≠ 0) (h4 : tan(-x+145*pi/2)≠ 0) (h5 : cos(-x+145*pi/2)≠ 0) (h6 : (sin(x+2*pi)*cos(pi-x)*cos(-x+145*pi/2))≠ 0) : -sin(-x)*sin(-x + 145*pi/2)*sin(x + 3*pi)*cos(x + pi)/(sin(x + 2*pi)*cos(pi - x)*cos(-x + 145*pi/2))=-cos(x):=
begin
have : sin(-x) * sin(-x + 145 * pi / 2) * -sin(x + 3 * pi) * cos(x + pi) / (sin(x + 2 * pi) * cos(pi - x) * cos(-x + 145 * pi / 2)) = -sin(-x)*sin(-x + 145*pi/2)*sin(x + 3*pi)*cos(x + pi)/(sin(x + 2*pi)*cos(pi - x)*cos(-x + 145*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + pi/2) = -sin(x + 3*pi),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x) * cos(-x + pi / 2) * cos(x + pi) * (sin(-x + 145 * pi / 2) / cos(-x + 145 * pi / 2)) / (sin(x + 2 * pi) * cos(pi - x)) = sin(-x)*sin(-x + 145*pi/2)*cos(-x + pi/2)*cos(x + pi)/(sin(x + 2*pi)*cos(pi - x)*cos(-x + 145*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-x + 145*pi/2) = sin(-x + 145*pi/2) / cos(-x + 145*pi/2),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sin(-x) * cos(-x + pi / 2) * cos(x + pi) / (sin(x + 2 * pi) * cos(pi - x) * (1 / tan(-x + 145 * pi / 2))) = sin(-x)*cos(-x + pi/2)*cos(x + pi)*tan(-x + 145*pi/2)/(sin(x + 2*pi)*cos(pi - x)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi) = 1 / tan(-x + 145*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (x + pi) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + pi/2) = sin(x),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + 2*pi) = sin(x),
{
rw sin_eq_sin_add_int_mul_two_pi (x + 2*pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(pi - x) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(x + pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
rw tan_eq_sin_div_cos,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_164_HNWO_extend(h0 : sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : sin(pi/9) ≠ 0) (h3 : sin(4*pi/9)≠ 0) (h4 : sin(2825*pi/18)≠ 0) (h5 : cos(973*pi/18)≠ 0) (h6 : -sin(175*pi/9)≠ 0) (h7 : sin(175*pi/9)≠ 0) : sqrt(3)/sin(175*pi/9) + 1/sin(2825*pi/18)=4:=
begin
have : -sqrt 3 / -sin(175 * pi / 9) + 1 / sin(2825 * pi / 18) = sqrt(3)/sin(175*pi/9) + 1/sin(2825*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(973*pi/18) = -sin(175*pi/9),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (973*pi/18) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 / cos(973 * pi / 18) + 1 / sin(2825 * pi / 18) = -sqrt(3)/cos(973*pi/18) + 1/sin(2825*pi/18),
{
field_simp at *,
},
have : sin(4*pi/9) = cos(973*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 / sin(4 * pi / 9) + 1 / sin(2825 * pi / 18) = -sqrt(3)/sin(4*pi/9) + 1/sin(2825*pi/18),
{
field_simp at *,
},
have : sin(pi/18) = sin(2825*pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/18) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = cos(pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sqrt(3)/cos(pi/18) + 1/sin(pi/18) = (-sqrt(3)*sin(pi/18) + cos(pi/18))/(sin(pi/18)*cos(pi/18)),
{
ring_exp,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
left,
ring_exp,
},
rw this,
rw neg_mul,
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*sin(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*cos(pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/18)*(2*cos(pi/18)*cos(pi/3)) = sin(pi/18)*cos(pi/18),
{
field_simp,
ring_exp,
},
rw this,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/18)*sin(pi/3) + 2*cos(pi/18)*cos(pi/3) = 2*cos(7*pi/18),
{
have : cos(7*pi/18) = -sin(pi/18)*sin(pi/3) + cos(pi/18)*cos(pi/3),
{
have : cos(7*pi/18) = cos((pi/3) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
have : cos(7*pi/18) = sin(pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/18)*cos(pi/18) = sin(pi/9)/2,
{
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
field_simp,
ring,
end


lemma Trigo_1_165_HETW_extend(h0 : cos(73*pi/180) ≠ 0) (h1 : cos(31*pi/90) ≠ 0) (h2 : 1 - tan(31*pi/90) * tan(73*pi/180) ≠ 0)  (h3 : cos(31*pi/90)≠ 0) (h4 : cos(17353*pi/180)≠ 0) (h5 : tan((31*pi/90)-(17353*pi/180))≠ 0) (h6 : 1+tan(31*pi/90)*tan(17353*pi/180)≠ 0) (h7 : tan((-17291)*pi/180)≠ 0) (h8 : tan(-17291*pi/180)≠ 0) (h9 : cos(17353*pi/180)≠ 0) (h10 : cos(31*pi/90)≠ 0) (h11 : 1 + tan(17353*pi/180) * tan(31*pi/90)≠ 0) : (1 + tan(31*pi/90)*tan(17353*pi/180))*tan(17291*pi/180)/tan(-17291*pi/180) + 1 + tan(31*pi/90) + tan(17353*pi/180)=-1:=
begin
have : (tan(17353 * pi / 180) * tan(31 * pi / 90) + 1) * tan(17291 * pi / 180) / tan((-17291) * pi / 180) + 1 + tan(31 * pi / 90) + tan(17353 * pi / 180) = (1 + tan(31*pi/90)*tan(17353*pi/180))*tan(17291*pi/180)/tan(-17291*pi/180) + 1 + tan(31*pi/90) + tan(17353*pi/180),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(17353*pi/180) - tan(31*pi/90) = ( tan(17353*pi/180) * tan(31*pi/90) + 1 ) * tan(17291*pi/180),
{
rw tan_sub_tan,
have : tan((17353*pi/180) - (31*pi/90)) = tan(17291*pi/180),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(17353*pi/180) - tan(31*pi/90))/tan(-17291*pi/180) + 1 + tan(31*pi/90) + tan(17353*pi/180) = -(-tan(17353*pi/180)+tan(31*pi/90))/tan(-17291*pi/180)+1+tan(31*pi/90)+tan(17353*pi/180),
{
ring,
},
conv {to_lhs, rw this,},
have : -((tan(31 * pi / 90) - tan(17353 * pi / 180)) / tan((-17291) * pi / 180) - 1) + tan(31 * pi / 90) + tan(17353 * pi / 180) = -(-tan(17353*pi/180) + tan(31*pi/90))/tan(-17291*pi/180) + 1 + tan(31*pi/90) + tan(17353*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(31*pi/90) * tan(17353*pi/180) = ( tan(31*pi/90) - tan(17353*pi/180) ) / tan(-17291*pi/180) - 1,
{
rw tan_mul_tan,
have : tan((31*pi/90) - (17353*pi/180)) = tan(-17291*pi/180),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -(tan(31*pi/90) * tan(17353*pi/180)) = -tan(31*pi/90)*tan(17353*pi/180),
{
ring,
},
conv {to_lhs, rw this,},
have : tan(73*pi/180) = tan(17353*pi/180),
{
rw tan_eq_tan_add_int_mul_pi (73*pi/180) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(31*pi/90) + tan(73*pi/180) = (-tan(31*pi/90)*tan(73*pi/180) + 1)*tan(3*pi/4),
{
rw tan_add_tan,
have : tan((31*pi/90) + (73*pi/180)) = tan(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(31*pi/90)*tan(73*pi/180) + 1)*tan(3*pi/4) = tan(3*pi/4) - tan(31*pi/90)*tan(73*pi/180)*tan(3*pi/4),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_four, -cos_pi_div_four],
ring_exp,
},
rw this,
have : tan(3*pi/4) = -tan(pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_four,
norm_num,
ring_exp,
end


lemma Trigo_1_166_WAWI_extend(h0 : cos(19*pi/180) ≠ 0) (h1 : cos(13*pi/90) ≠ 0) (h2 : 1 - tan(13*pi/90) * tan(19*pi/180) ≠ 0)  (h3 : cos((19*pi/90)/2)≠ 0) (h4 : sin(19*pi/90)≠ 0) (h5 : sin(14419*pi/90)≠ 0) : (sin(-13*pi/45)*sin(pi/2) - cos(-13*pi/45)*cos(pi/2) + 1)*tan(13*pi/90)/sin(14419*pi/90) + (sin(-13*pi/45)*sin(pi/2) - cos(-13*pi/45)*cos(pi/2) + 1)/sin(14419*pi/90) + tan(13*pi/90)=1:=
begin
have : (1 - (-sin((-13) * pi / 45) * sin(pi / 2) + cos((-13) * pi / 45) * cos(pi / 2))) * tan(13 * pi / 90) / sin(14419 * pi / 90) + (1 - (-sin((-13) * pi / 45) * sin(pi / 2) + cos((-13) * pi / 45) * cos(pi / 2))) / sin(14419 * pi / 90) + tan(13 * pi / 90) = (sin(-13*pi/45)*sin(pi/2) - cos(-13*pi/45)*cos(pi/2) + 1)*tan(13*pi/90)/sin(14419*pi/90) + (sin(-13*pi/45)*sin(pi/2) - cos(-13*pi/45)*cos(pi/2) + 1)/sin(14419*pi/90) + tan(13*pi/90),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(19*pi/90) = -sin(-13*pi/45) * sin(pi/2) + cos(-13*pi/45) * cos(pi/2),
{
have : cos(19*pi/90) = cos((-13*pi/45) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(19*pi/90) = sin(14419*pi/90),
{
rw sin_eq_sin_add_int_mul_two_pi (19*pi/90) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos(19 * pi / 90)) / sin(19 * pi / 90) * tan(13 * pi / 90) + (1 - cos(19 * pi / 90)) / sin(19 * pi / 90) + tan(13 * pi / 90) = (1 - cos(19*pi/90))*tan(13*pi/90)/sin(19*pi/90) + (1 - cos(19*pi/90))/sin(19*pi/90) + tan(13*pi/90),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(19*pi/180) = ( 1 - cos(19*pi/90) ) / sin(19*pi/90),
{
have : tan(19*pi/180) = tan((19*pi/90)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(19*pi/180) + tan(13*pi/90) = (-tan(19*pi/180)*tan(13*pi/90) + 1)*tan(pi/4),
{
rw add_comm,
rw tan_add_tan,
have : tan((13*pi/90) + (19*pi/180)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(19*pi/180)*tan(13*pi/90) + 1)*tan(pi/4) = -tan(19*pi/180)*tan(13*pi/90)*tan(pi/4) + tan(pi/4),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_four, -cos_pi_div_four],
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_1_167_EBUX_extend(h0 : cos(x) ≠ 0) (h1 : cos(2*x) ≠ 0) (h2 : ((cos(-2*x+44*pi)+1)*cos(-2*x+44*pi))≠ 0) (h3 : ((cos((-2)*x+44*pi)+1)*cos((-2)*x+44*pi))≠ 0) (h4 : cos(2*x)≠ 0) : -2*cos(x)**2*cos(2*x + 13*pi/2)/((cos(-2*x + 44*pi) + 1)*cos(-2*x + 44*pi))=sin(2*x)/cos(2*x):=
begin
have : tan(2*x) = sin(2*x) / cos(2*x),
{
rw tan_eq_sin_div_cos,
},
conv {to_rhs, rw ← this,},
have : 2 * -cos(2 * x + 13 * pi / 2) * cos(x) ** 2 / ((cos((-2) * x + 44 * pi) + 1) * cos((-2) * x + 44 * pi)) = -2*cos(x)**2*cos(2*x + 13*pi/2)/((cos(-2*x + 44*pi) + 1)*cos(-2*x + 44*pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x) = -cos(2*x + 13*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*x) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(2 * x) * cos(x) ** 2 / ((cos((-2) * x + 44 * pi) + 1) * cos((-2) * x + 44 * pi)) = 2*sin(2*x)*cos(x)**2/((cos(-2*x + 44*pi) + 1)*cos(-2*x + 44*pi)),
{
field_simp at *,
},
have : cos(2*x) = cos(-2*x + 44*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*x) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : cos(2*x) + 1 = 2*cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_1_168_GBIJ_extend : (sin(pi)*cos(-137*pi/180) + sin(-137*pi/180)*cos(pi))*cos(167*pi/180) - 2*sin(13*pi/360)*cos(43*pi/180)*cos(11893*pi/360)=-1/2:=
begin
have : (sin((-137) * pi / 180) * cos(pi) + sin(pi) * cos((-137) * pi / 180)) * cos(167 * pi / 180) - 2 * sin(13 * pi / 360) * cos(43 * pi / 180) * cos(11893 * pi / 360) = (sin(pi)*cos(-137*pi/180) + sin(-137*pi/180)*cos(pi))*cos(167*pi/180) - 2*sin(13*pi/360)*cos(43*pi/180)*cos(11893*pi/360),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi/180) = sin(-137*pi/180) * cos(pi) + sin(pi) * cos(-137*pi/180),
{
have : sin(43*pi/180) = sin((-137*pi/180) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(43 * pi / 180) * cos(167 * pi / 180) + 2 * sin(13 * pi / 360) * -cos(11893 * pi / 360) * cos(43 * pi / 180) = sin(43*pi/180)*cos(167*pi/180) - 2*sin(13*pi/360)*cos(43*pi/180)*cos(11893*pi/360),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/360) = -cos(11893*pi/360),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (13*pi/360) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(13 * pi / 360) * cos(13 * pi / 360) * cos(43 * pi / 180) + sin(43 * pi / 180) * cos(167 * pi / 180) = sin(43*pi/180)*cos(167*pi/180) + 2*sin(13*pi/360)*cos(13*pi/360)*cos(43*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = 2 * sin(13*pi/360) * cos(13*pi/360),
{
have : sin(13*pi/180) = sin(2*(13*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(167*pi/180) = -cos(13*pi/180),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (167*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_neg,
rw ← neg_mul,
have : -sin(43*pi/180)*cos(13*pi/180) + sin(13*pi/180)*cos(43*pi/180) = sin(-pi/6),
{
have : sin(-pi/6) = sin((13*pi/180) - (43*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(-pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_1_169_PTGK_extend(h0: cos(2) + sin(2) ≥ 0) : sqrt((-3*cos(2/3) + 4*cos(2/3)**3)*(-2*sin(2*pi)*cos(2 + 2*pi) + sin(2) + sin(2 + 4*pi)) + 1)=sin(2)+cos(2):=
begin
have : sqrt (((-2) * sin(2 * pi) * cos(2 + 2 * pi) + 2 * (sin(2) / 2 + sin(2 + 4 * pi) / 2)) * ((-3) * cos(2 / 3) + 4 * cos(2 / 3) ** 3) + 1) = sqrt((-3*cos(2/3) + 4*cos(2/3)**3)*(-2*sin(2*pi)*cos(2 + 2*pi) + sin(2) + sin(2 + 4*pi)) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 + 2*pi) * cos(2*pi) = sin(2) / 2 + sin(2 + 4*pi) / 2,
{
rw sin_mul_cos,
have : sin((2 + 2*pi) + (2*pi)) = sin(2 + 4*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2 + 2*pi) - (2*pi)) = sin(2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 2*(sin(2 + 2*pi) * cos(2*pi)) = 2*sin(2+2*pi)*cos(2*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : sqrt (2 * (-sin(2 * pi) * cos(2 + 2 * pi) + sin(2 + 2 * pi) * cos(2 * pi)) * (4 * cos(2 / 3) ** 3 - 3 * cos(2 / 3)) + 1) = sqrt((-2*sin(2*pi)*cos(2 + 2*pi) + 2*sin(2 + 2*pi)*cos(2*pi))*(-3*cos(2/3) + 4*cos(2/3)**3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2) = 4 * cos(2/3) ** 3 - 3 * cos(2/3),
{
have : cos(2) = cos(3*(2/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sqrt (2 * (sin(2 + 2 * pi) * cos(2 * pi) - sin(2 * pi) * cos(2 + 2 * pi)) * cos(2) + 1) = sqrt(2*(-sin(2*pi)*cos(2 + 2*pi) + sin(2 + 2*pi)*cos(2*pi))*cos(2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2) = sin(2 + 2*pi) * cos(2*pi) - sin(2*pi) * cos(2 + 2*pi),
{
have : sin(2) = sin((2 + 2*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*sin(2)*cos(2) + 1 = 2*sin(2)*cos(2) + cos(2)**2 + sin(2)**2,
{
rw add_assoc,
rw cos_sq_add_sin_sq,
},
rw this,
have : 2*sin(2)*cos(2) + cos(2)**2 + sin(2)**2 = (cos(2) + sin(2))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
ring,
end


lemma Trigo_1_170_YMAF_extend(h0 : 1-tan(pi/9)*tan(pi/18) ≠ 0) (h1 : tan((pi/9)+(pi/18)) ≠ 0) (h2 : cos(pi/18) ≠ 0) (h3 : cos(pi/9) ≠ 0) (h4 : sqrt 3 ≠ 0) (h5 : cos(pi/9)≠ 0) : sin(pi/9)*tan(433*pi/18)/cos(pi/9) + sqrt(3)*(tan(433*pi/18) + sin(pi/9)/cos(pi/9))=1:=
begin
have : -sin(pi / 9) * -tan(433 * pi / 18) / cos(pi / 9) + sqrt 3 * (- -tan(433 * pi / 18) + sin(pi / 9) / cos(pi / 9)) = sin(pi/9)*tan(433*pi/18)/cos(pi/9) + sqrt(3)*(tan(433*pi/18) + sin(pi/9)/cos(pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/18) = -tan(433*pi/18),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/18) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -tan(-pi / 18) * (sin(pi / 9) / cos(pi / 9)) + sqrt 3 * (-tan(-pi / 18) + sin(pi / 9) / cos(pi / 9)) = -sin(pi/9)*tan(-pi/18)/cos(pi/9) + sqrt(3)*(-tan(-pi/18) + sin(pi/9)/cos(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = sin(pi/9) / cos(pi/9),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * (-tan(-pi / 18) + tan(pi / 9)) + -tan(-pi / 18) * tan(pi / 9) = -tan(-pi/18)*tan(pi/9) + sqrt(3)*(-tan(-pi/18) + tan(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = -tan(-pi/18),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/18) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18)*tan(pi/9) = -(tan(pi/18) + tan(pi/9))/tan(pi/6) + 1,
{
rw mul_comm,
rw tan_mul_tan',
have : tan((pi/9) + (pi/18)) = tan(pi/6),
{
apply congr_arg,
ring,
},
rw this,
field_simp,
left,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_six,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_1_171_MLEC_extend(h0 : sin(x) ≠ 0) (h1 : tan(x) ≠ 0) (h2 : sin(x+pi)≠ 0) (h3 : cos(-x + 3*pi/2)≠ 0) (h4 : cos(x)≠ 0) (h5 : tan((-x + 3*pi/2)-(x))≠ 0) (h6 : 1+tan(-x + 3*pi/2)*tan(x)≠ 0) (h7 : tan((-2)*x+3*pi/2)≠ 0) (h8 : tan(-2*x+3*pi/2)≠ 0) (h9 : (-4*sin(x/3+pi/3)**3+3*sin(x/3+pi/3))≠ 0) (h10 : ((-4)*sin(x/3+pi/3)**3+3*sin(x/3+pi/3))≠ 0) : (-(-tan(x) + tan(-x + 3*pi/2))/tan(-2*x + 3*pi/2) + 1)*cos(-x + 2*pi)*cos(-x + 359*pi/2)/(-4*sin(x/3 + pi/3)**3 + 3*sin(x/3 + pi/3))=-cos(x):=
begin
have : -((-tan(x) + tan(-x + 3 * pi / 2)) / tan((-2) * x + 3 * pi / 2) - 1) * cos(-x + 2 * pi) * cos(-x + 359 * pi / 2) / ((-4) * sin(x / 3 + pi / 3) ** 3 + 3 * sin(x / 3 + pi / 3)) = (-(-tan(x) + tan(-x + 3*pi/2))/tan(-2*x + 3*pi/2) + 1)*cos(-x + 2*pi)*cos(-x + 359*pi/2)/(-4*sin(x/3 + pi/3)**3 + 3*sin(x/3 + pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) = -4 * sin(x/3 + pi/3) ** 3 + 3 * sin(x/3 + pi/3),
{
have : sin(x + pi) = sin(3*(x/3 + pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : -((tan(-x + 3 * pi / 2) - tan(x)) / tan((-2) * x + 3 * pi / 2) - 1) * cos(-x + 2 * pi) * cos(-x + 359 * pi / 2) / sin(x + pi) = -((-tan(x) + tan(-x + 3*pi/2))/tan(-2*x + 3*pi/2) - 1)*cos(-x + 2*pi)*cos(-x + 359*pi/2)/sin(x + pi),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-x + 3*pi/2) * tan(x) = ( tan(-x + 3*pi/2) - tan(x) ) / tan(-2*x + 3*pi/2) - 1,
{
rw tan_mul_tan,
have : tan((-x + 3*pi/2) - (x)) = tan(-2*x + 3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -(tan(-x + 3*pi/2) * tan(x))*cos(-x + 2*pi)*cos(-x + 359*pi/2)/sin(x + pi) = -cos(-x+2*pi)*cos(-x+359*pi/2)*tan(x)*tan(-x+3*pi/2)/sin(x+pi),
{
ring,
},
conv {to_lhs, rw this,},
have : -cos(-x + 359 * pi / 2) * cos(-x + 2 * pi) * tan(x) * tan(-x + 3 * pi / 2) / sin(x + pi) = -cos(-x + 2*pi)*cos(-x + 359*pi/2)*tan(x)*tan(-x + 3*pi/2)/sin(x + pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = -cos(-x + 359*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi - x) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x + 3*pi/2) = 1/tan(x),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw div_neg,
field_simp,
ring_exp,
end


lemma Trigo_1_172_FYAM_extend : (sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12))*cos(3*pi/4) + (sin(2*pi)*cos(-7*pi/4) + sin(-7*pi/4)*cos(2*pi))*sin(1903*pi/12)=1/2:=
begin
have : (sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12)) * cos(3 * pi / 4) + (sin(2 * pi) * cos((-7) * pi / 4) + sin((-7) * pi / 4) * cos(2 * pi)) * sin(1903 * pi / 12) = (sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12))*cos(3*pi/4) + (sin(2*pi)*cos(-7*pi/4) + sin(-7*pi/4)*cos(2*pi))*sin(1903*pi/12),
{
field_simp at *,
},
have : cos(pi/12) = sin(1903*pi/12),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/12) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12)) * cos(3 * pi / 4) + (sin((-7) * pi / 4) * cos(2 * pi) + sin(2 * pi) * cos((-7) * pi / 4)) * cos(pi / 12) = (sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12))*cos(3*pi/4) + (sin(2*pi)*cos(-7*pi/4) + sin(-7*pi/4)*cos(2*pi))*cos(pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(-7*pi/4) * cos(2*pi) + sin(2*pi) * cos(-7*pi/4),
{
have : sin(pi/4) = sin((-7*pi/4) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-5) * pi / 12) * cos(pi / 2) + sin(pi / 2) * cos((-5) * pi / 12)) * cos(3 * pi / 4) + sin(pi / 4) * cos(pi / 12) = (sin(-5*pi/12)*cos(pi/2) + sin(pi/2)*cos(-5*pi/12))*cos(3*pi/4) + sin(pi/4)*cos(pi/12),
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
have : cos(3*pi/4) = -cos(pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_neg,
rw ← neg_mul,
have : -sin(pi/12)*cos(pi/4) + sin(pi/4)*cos(pi/12) = sin(pi/6),
{
have : sin(pi/6) = sin((pi/4) - (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_1_173_HJXB_extend : 2*sin(-13*pi/360)*sin(73*pi/180)*sin(38713*pi/360) + sin(103*pi/180)*sin(163*pi/180)=1/2:=
begin
have : (-2) * sin((-13) * pi / 360) * sin(73 * pi / 180) * -sin(38713 * pi / 360) + sin(103 * pi / 180) * sin(163 * pi / 180) = 2*sin(-13*pi/360)*sin(73*pi/180)*sin(38713*pi/360) + sin(103*pi/180)*sin(163*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/360) = -sin(38713*pi/360),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/360) (53),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * -sin((-13) * pi / 360) * sin(73 * pi / 180) * cos(13 * pi / 360) + sin(103 * pi / 180) * sin(163 * pi / 180) = -2*sin(-13*pi/360)*sin(73*pi/180)*cos(13*pi/360) + sin(103*pi/180)*sin(163*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/360) = -sin(-13*pi/360),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (13*pi/360) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(13 * pi / 360) * cos(13 * pi / 360) * sin(73 * pi / 180) + sin(103 * pi / 180) * sin(163 * pi / 180) = 2*sin(13*pi/360)*sin(73*pi/180)*cos(13*pi/360) + sin(103*pi/180)*sin(163*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = 2 * sin(13*pi/360) * cos(13*pi/360),
{
have : sin(13*pi/180) = sin(2*(13*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(103*pi/180) = cos(13*pi/180),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (103*pi/180) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(163*pi/180) = sin(17*pi/180),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (163*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(73*pi/180) = cos(17*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (73*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_comm (cos(13*pi/180)) (sin(17*pi/180)),
have : sin(13*pi/180)*cos(17*pi/180) + sin(17*pi/180)*cos(13*pi/180) = sin(pi/6),
{
have : sin(pi/6) = sin((13*pi/180) + (17*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_1_175_HAOV_extend (h0 : cos(77*pi/180)≠ 0) (h1 : (2*cos(77*pi/180))≠ 0) : (1 - 2*cos(47*pi/360)**2)*sin(77*pi/90)/(2*cos(77*pi/180)) + sin(13*pi/180)*cos(31363*pi/180)=-1/2:=
begin
have : -(-1 + 2 * cos(47 * pi / 360) ** 2) * (sin(77 * pi / 90) / (2 * cos(77 * pi / 180))) + sin(13 * pi / 180) * cos(31363 * pi / 180) = (1 - 2*cos(47*pi/360)**2)*sin(77*pi/90)/(2*cos(77*pi/180)) + sin(13*pi/180)*cos(31363*pi/180),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(77*pi/180) = sin(77*pi/90) / ( 2 * cos(77*pi/180) ),
{
have : sin(77*pi/90) = sin(2*(77*pi/180)),
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
have : -sin(77 * pi / 180) * (2 * cos(47 * pi / 360) ** 2 - 1) + sin(13 * pi / 180) * cos(31363 * pi / 180) = -(-1 + 2*cos(47*pi/360)**2)*sin(77*pi/180) + sin(13*pi/180)*cos(31363*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(47*pi/180) = 2 * cos(47*pi/360) ** 2 - 1,
{
have : cos(47*pi/180) = cos(2*(47*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 180) * cos(31363 * pi / 180) - sin(77 * pi / 180) * cos(47 * pi / 180) = -sin(77*pi/180)*cos(47*pi/180) + sin(13*pi/180)*cos(31363*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(47*pi/180) = cos(31363*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (47*pi/180) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(77*pi/180) = cos(13*pi/180),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (77*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sub_eq_neg_add,
rw ← neg_mul,
have : -cos(13*pi/180)*cos(47*pi/180) + sin(13*pi/180)*sin(47*pi/180) = -cos(pi/3),
{
have : cos(pi/3) = -sin(13*pi/180)*sin(47*pi/180) + cos(13*pi/180)*cos(47*pi/180),
{
have : cos(pi/3) = cos((13*pi/180) + (47*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_1_176_WMJO_extend(h0 : cos (pi/8) ≠ 0)  (h2 : cos((pi/4)/2)≠ 0) (h3 : (1+cos(pi/4))≠ 0) (h4 : (cos(pi/4)+1)≠ 0) (h5 : (2*cos(pi/8)**2-1+1)≠ 0) (h6 : (2*cos(pi/8)**2)≠ 0) (h7 : (2*(1-2*sin(pi/16)**2)**2)≠ 0) : sin(pi/4)/(2*(1 - 2*sin(pi/16)**2)**2)=sqrt(2)-1:=
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
have : sin(pi / 4) / (2 * cos(pi / 8) ** 2 - 1 + 1) = sin(pi/4)/(2*cos(pi/8)**2),
{
field_simp at *,
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
have : sin(pi / 4) / (1 + cos(pi / 4)) = sin(pi/4)/(cos(pi/4) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = sin(pi/4) / ( 1 + cos(pi/4) ),
{
have : tan(pi/8) = tan((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = (1 - cos(pi/4))/sin(pi/4),
{
have : cos(pi/8) = cos((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this at *,
have : tan(pi/8) = tan((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_1_177_THTG_extend : (1 - 2*cos(445*pi/24)**2)*sin(pi/12)*sin(pi/6)=1/8:=
begin
have : -(1 - 2 * (1 - cos(445 * pi / 24) ** 2)) * sin(pi / 12) * sin(pi / 6) = (1 - 2*cos(445*pi/24)**2)*sin(pi/12)*sin(pi/6),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(445*pi/24) ** 2 = 1 - cos(445*pi/24) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 12) * sin(pi / 6) * (1 - 2 * sin(445 * pi / 24) ** 2) = -(1 - 2*sin(445*pi/24)**2)*sin(pi/12)*sin(pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(445*pi/12) = 1 - 2 * sin(445*pi/24) ** 2,
{
have : cos(445*pi/12) = cos(2*(445*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) * sin(pi / 6) * -cos(445 * pi / 12) = -sin(pi/12)*sin(pi/6)*cos(445*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = -cos(445*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/12) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_right_comm,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_1_178_MWGJ_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : cos(x) + 1 ≠ 0)  (h3 : tan(x)≠ 0) (h4 : (1/tan(x)+1/sin(x+102*pi))≠ 0) (h5 : sin(x+102*pi)≠ 0) (h6 : cos(x + 102*pi)≠ 0) (h7 : (1/tan(x)+2*cos(x+102*pi)/sin(2*x+204*pi))≠ 0) (h8 : (1/tan(x)+1/(sin(2*x+204*pi)/(2*cos(x+102*pi))))≠ 0) (h9 : (2*cos(x+102*pi))≠ 0) (h10 : (sin(2*x+204*pi)/(2*cos(x+102*pi)))≠ 0) (h11 : sin(2*x+204*pi)≠ 0) (h12 : (2*sin(x+313*pi/2)/sin(2*x+204*pi)+1/tan(x))≠ 0) (h13 : (1/tan(x)+2*sin(x+313*pi/2)/sin(2*x+204*pi))≠ 0) (h14 : (2*sin(x+313*pi/2))≠ 0) : (cos(x) - sin(2*x + 204*pi)/(2*sin(x + 313*pi/2)))*tan(x) + (tan(x) + sin(2*x + 204*pi)/(2*sin(x + 313*pi/2)))/(2*sin(x + 313*pi/2)/sin(2*x + 204*pi) + 1/tan(x))=sin(x):=
begin
have : (-sin(2 * x + 204 * pi) / (2 * sin(x + 313 * pi / 2)) + cos(x)) * tan(x) + (sin(2 * x + 204 * pi) / (2 * sin(x + 313 * pi / 2)) + tan(x)) / (1 / tan(x) + 2 * sin(x + 313 * pi / 2) / sin(2 * x + 204 * pi)) = (cos(x) - sin(2*x + 204*pi)/(2*sin(x + 313*pi/2)))*tan(x) + (tan(x) + sin(2*x + 204*pi)/(2*sin(x + 313*pi/2)))/(2*sin(x + 313*pi/2)/sin(2*x + 204*pi) + 1/tan(x)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 102*pi) = sin(x + 313*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x + 102*pi) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-(sin(2 * x + 204 * pi) / (2 * cos(x + 102 * pi))) + cos(x)) * tan(x) + (sin(2 * x + 204 * pi) / (2 * cos(x + 102 * pi)) + tan(x)) / (1 / tan(x) + 1 / (sin(2 * x + 204 * pi) / (2 * cos(x + 102 * pi)))) = (-sin(2*x + 204*pi)/(2*cos(x + 102*pi)) + cos(x))*tan(x) + (sin(2*x + 204*pi)/(2*cos(x + 102*pi)) + tan(x))/(1/tan(x) + 2*cos(x + 102*pi)/sin(2*x + 204*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x + 102*pi) = sin(2*x + 204*pi) / ( 2 * cos(x + 102*pi) ),
{
have : sin(2*x + 204*pi) = sin(2*(x + 102*pi)),
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
have : sin(x) = sin(x + 102*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (x) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw ← mul_div_assoc,
have : (-sin(x) + cos(x))*sin(x)/cos(x) = -sin(x)**2/cos(x) + sin(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sin(x) + sin(x)/cos(x) = (sin(x)*cos(x) + sin(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
norm_num,
have : cos(x)/sin(x) + 1/sin(x) = (cos(x) + 1)/sin(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : sin(x)*cos(x) + sin(x) = (cos(x) + 1)*sin(x),
{
ring_exp,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_1_179_LPWJ_extend(h0: -sin 2 + cos 2 ≤ 0)  : sqrt(2*sin(-2 + 2*pi)*sin(-2 + 57*pi/2) + 1)=-sin(-2 + 261*pi/2) + sin(2):=
begin
have : sin(2) - sin(-2 + 261 * pi / 2) = -sin(-2 + 261*pi/2) + sin(2),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2) = sin(-2 + 261*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sqrt ((-2) * sin(-2 + 2 * pi) * -sin(-2 + 57 * pi / 2) + 1) = sqrt(2*sin(-2 + 2*pi)*sin(-2 + 57*pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2 + 187*pi/2) = -sin(-2 + 57*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2 + 187*pi/2) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (2 * sin(-2 + 2 * pi) * -sin(2 + 187 * pi / 2) + 1) = sqrt(-2*sin(-2 + 2*pi)*sin(2 + 187*pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-2 + 2*pi) = -sin(2 + 187*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-2 + 2*pi) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*sin(-2 + 2*pi)*cos(-2 + 2*pi) = sin(-4 + 4*pi),
{
have : sin(-4 + 4*pi) = sin(2*(-2 + 2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(-4 + 4*pi) = 2*sin(-2 + 2*pi)*cos(-2 + 2*pi),
{
have : sin(-4 + 4*pi) = sin(2*(-2 + 2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : 2*sin(-2 + 2*pi)*cos(-2 + 2*pi) + 1 = 2*sin(-2 + 2*pi)*cos(-2 + 2*pi) + cos(-2 + 2*pi)**2 + sin(-2 + 2*pi)**2,
{
rw add_assoc,
rw cos_sq_add_sin_sq,
},
rw this,
have : 2*sin(-2 + 2*pi)*cos(-2 + 2*pi) + cos(-2 + 2*pi)**2 + sin(-2 + 2*pi)**2 = (sin(-2 + 2*pi) + cos(-2 + 2*pi))**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sin(-2 + 2*pi) = -sin(2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2 + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-2 + 2*pi) = cos(2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2 + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h0,
ring,
end


lemma Trigo_1_180_DFLS_extend(h0 : -cos(pi/9) + sin(pi/9) ≠ 0) (h1 : cos(pi/9) ≥ 0) (h2 : -cos(pi/9) + sin(pi/9) ≤ 0)  (h3 : (-sqrt(1-sin(pi/9)**2)+sin(8*pi/9))≠ 0) (h4 : (-sqrt(cos(2*pi/9)/2+1/2)+sin(8*pi/9))≠ 0) (h5 : (-sqrt(1-(1/2-cos(2*pi/9)/2))+sin(8*pi/9))≠ 0) (h6 : (-sqrt(cos(2*pi/9)/2+1/2)+cos(893*pi/18))≠ 0) : sqrt(-2*sin(pi/9)*sin(2027*pi/18) + 1)/(-sqrt(cos(2*pi/9)/2 + 1/2) + cos(893*pi/18))=-1:=
begin
have : sqrt ((-2) * sin(pi / 9) * sin(2027 * pi / 18) + 1) / (-sqrt (cos(2 * pi / 9) / 2 + 1 / 2) + cos(893 * pi / 18)) = sqrt(-2*sin(pi/9)*sin(2027*pi/18) + 1)/(-sqrt(cos(2*pi/9)/2 + 1/2) + cos(893*pi/18)),
{
field_simp at *,
},
have : sin(8*pi/9) = cos(893*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (8*pi/9) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 9) * sin(2027 * pi / 18) + 1) / (-sqrt (1 - (1 / 2 - cos(2 * pi / 9) / 2)) + sin(8 * pi / 9)) = sqrt(-2*sin(pi/9)*sin(2027*pi/18) + 1)/(-sqrt(cos(2*pi/9)/2 + 1/2) + sin(8*pi/9)),
{
field_simp at *,
repeat {left},
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
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 9) * sin(2027 * pi / 18) + 1) / (-sqrt (1 - sin(pi / 9) ** 2) + sin(8 * pi / 9)) = sqrt(-2*sin(pi/9)*sin(2027*pi/18) + 1)/(-sqrt(1 - sin(pi/9)**2) + sin(8*pi/9)),
{
field_simp at *,
},
have : cos(pi/9) = sin(2027*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/9) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -2*sin(pi/9)*cos(pi/9) + 1 = -2*sin(pi/9)*cos(pi/9) + sin(pi/9)**2 + cos(pi/9)**2,
{
rw add_assoc,
rw sin_sq_add_cos_sq,
},
rw this,
have : -2*sin(pi/9)*cos(pi/9) + sin(pi/9)**2 + cos(pi/9)**2 = (-cos(pi/9) + sin(pi/9))**2,
{
ring_exp,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h2,
have : 1 - sin(pi / 9) ** 2 = cos(pi/9)**2,
{
rw cos_sq',
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h1,
field_simp,
end


lemma Trigo_1_181_YEAI_extend(h0 : cos(y) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (sin(y+5*pi/2)*cos(x))≠ 0) (h3 : (cos(x)*sin(y+5*pi/2))≠ 0) (h4 : cos((2*y)/2)≠ 0) (h5 : (cos(2*y)+1)≠ 0) (h6 : (1+cos(2*y))≠ 0) : (-4*sin(x/3 - y/3)**3 + 3*sin(x/3 - y/3))/(sin(y + 5*pi/2)*cos(x)) - tan(x) + sin(2*y)/(cos(2*y) + 1)=0:=
begin
have : ((-4) * sin(x / 3 - y / 3) ** 3 + 3 * sin(x / 3 - y / 3)) / (sin(y + 5 * pi / 2) * cos(x)) - tan(x) + sin(2 * y) / (1 + cos(2 * y)) = (-4*sin(x/3 - y/3)**3 + 3*sin(x/3 - y/3))/(sin(y + 5*pi/2)*cos(x)) - tan(x) + sin(2*y)/(cos(2*y) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(y) = sin(2*y) / ( 1 + cos(2*y) ),
{
have : tan(y) = tan((2*y)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(x / 3 - y / 3) ** 3 + 3 * sin(x / 3 - y / 3)) / (sin(y + 5 * pi / 2) * cos(x)) - tan(x) + tan(y) = (-4*sin(x/3 - y/3)**3 + 3*sin(x/3 - y/3))/(sin(y + 5*pi/2)*cos(x)) - tan(x) + tan(y),
{
field_simp at *,
},
have : sin(x - y) = -4 * sin(x/3 - y/3) ** 3 + 3 * sin(x/3 - y/3),
{
have : sin(x - y) = sin(3*(x/3 - y/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - y) / (cos(x) * sin(y + 5 * pi / 2)) - tan(x) + tan(y) = sin(x - y)/(sin(y + 5*pi/2)*cos(x)) - tan(x) + tan(y),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(y) = sin(y + 5*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (y) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - y) = sin(x)*cos(y) - sin(y)*cos(x),
{
have : sin(x-y) = sin((x) - (y)),
{
apply congr_arg,
ring,
},
rw sin_sub,
ring,
},
rw this,
rw tan_eq_sin_div_cos,
rw tan_eq_sin_div_cos,
rw sub_eq_add_neg,
rw add_assoc,
rw neg_div',
have : -sin(x)/cos(x) + sin(y)/cos(y) = (-sin(x)*cos(y) + sin(y)*cos(x))/(cos(x)*cos(y)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
field_simp,
end


lemma Trigo_1_182_TJRB_extend(h0 : cos(x) ≠ 0) (h1 : cos(x)≠ 0) (h2 : (sin(x-pi/2)*sin(-pi/2)+cos(x-pi/2)*cos(-pi/2))≠ 0) (h3 : (sin(-pi/2)*sin(x-pi/2)+cos(-pi/2)*cos(x-pi/2))≠ 0) (h4 : (sin(-pi/2)*sin(x-pi/2)+(-1+2*cos(-pi/4)**2)*cos(x-pi/2))≠ 0) (h5 : (sin(-pi/2)*sin(x-pi/2)+(2*cos(-pi/4)**2-1)*cos(x-pi/2))≠ 0) : (sin(-x + 817*pi/6) + sin(x + pi/6))/(sin(-pi/2)*sin(x - pi/2) + (-1 + 2*cos(-pi/4)**2)*cos(x - pi/2))=1:=
begin
have : (sin(-x + 817 * pi / 6) + sin(x + pi / 6)) / (sin(-pi / 2) * sin(x - pi / 2) + (2 * cos(-pi / 4) ** 2 - 1) * cos(x - pi / 2)) = (sin(-x + 817*pi/6) + sin(x + pi/6))/(sin(-pi/2)*sin(x - pi/2) + (-1 + 2*cos(-pi/4)**2)*cos(x - pi/2)),
{
field_simp at *,
repeat {left},
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
have : (sin(-x + 817 * pi / 6) + sin(x + pi / 6)) / (sin(x - pi / 2) * sin(-pi / 2) + cos(x - pi / 2) * cos(-pi / 2)) = (sin(-x + 817*pi/6) + sin(x + pi/6))/(sin(-pi/2)*sin(x - pi/2) + cos(-pi/2)*cos(x - pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(x - pi/2) * sin(-pi/2) + cos(x - pi/2) * cos(-pi/2),
{
have : cos(x) = cos((x - pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/6) = sin(-x + 817*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (-x + pi/6) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/6) = -sin(x - pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(x - pi/6) + sin(x + pi/6) = 2*sin(pi/6)*cos(x),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((x + pi/6) + (x - pi/6))/2) = cos(x),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((x + pi/6) - (x - pi/6))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_pi_div_six,
field_simp,
end


lemma Trigo_1_183_DIYN_extend : sin(767*pi/12)*cos(1211*pi/12)=1/4:=
begin
have : - -sin(767 * pi / 12) * cos(1211 * pi / 12) = sin(767*pi/12)*cos(1211*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(457*pi/12) = -sin(767*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (457*pi/12) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(457 * pi / 12) * -cos(1211 * pi / 12) = -sin(457*pi/12)*cos(1211*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(1211*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 12) * sin(457 * pi / 12) = sin(457*pi/12)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(457*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_comm,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_1_184_ROGD_extend(h0 : cos(x) ≠ 0) (h1 : sin(x) ≠ 0) (h2 : ((2*cos(-x/2-pi/2)**2-1)*sin(-x-pi)*sin(x+pi/2))≠ 0) (h3 : (sin(-x-pi)*sin(x+pi/2)*(2*cos(-x/2-pi/2)**2-1))≠ 0) (h4 : ((2*cos(-x/2-pi/2)**2-1)*sin(x+pi/2)*cos(x+365*pi/2))≠ 0) (h5 : ((2*cos(-x/2-pi/2)**2-1)*-cos(x+365*pi/2)*sin(x+pi/2))≠ 0) : -(-sin(pi/3)*sin(-x + 5*pi/3) + cos(pi/3)*cos(-x + 5*pi/3))**2*sin(-x + 3*pi/2)*sin(x - 3*pi)/((2*cos(-x/2 - pi/2)**2 - 1)*sin(x + pi/2)*cos(x + 365*pi/2))=-cos(x):=
begin
have : (-sin(pi / 3) * sin(-x + 5 * pi / 3) + cos(pi / 3) * cos(-x + 5 * pi / 3)) ** 2 * sin(-x + 3 * pi / 2) * sin(x - 3 * pi) / ((2 * cos(-x / 2 - pi / 2) ** 2 - 1) * -cos(x + 365 * pi / 2) * sin(x + pi / 2)) = -(-sin(pi/3)*sin(-x + 5*pi/3) + cos(pi/3)*cos(-x + 5*pi/3))**2*sin(-x + 3*pi/2)*sin(x - 3*pi)/((2*cos(-x/2 - pi/2)**2 - 1)*sin(x + pi/2)*cos(x + 365*pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x - pi) = -cos(x + 365*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x - pi) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 3 * pi / 2) * sin(x - 3 * pi) * (-sin(-x + 5 * pi / 3) * sin(pi / 3) + cos(-x + 5 * pi / 3) * cos(pi / 3)) ** 2 / ((2 * cos(-x / 2 - pi / 2) ** 2 - 1) * sin(-x - pi) * sin(x + pi / 2)) = (-sin(pi/3)*sin(-x + 5*pi/3) + cos(pi/3)*cos(-x + 5*pi/3))**2*sin(-x + 3*pi/2)*sin(x - 3*pi)/((2*cos(-x/2 - pi/2)**2 - 1)*sin(-x - pi)*sin(x + pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = -sin(-x + 5*pi/3) * sin(pi/3) + cos(-x + 5*pi/3) * cos(pi/3),
{
have : cos(-x + 2*pi) = cos((-x + 5*pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 3 * pi / 2) * sin(x - 3 * pi) * cos(-x + 2 * pi) ** 2 / (sin(-x - pi) * sin(x + pi / 2) * (2 * cos(-x / 2 - pi / 2) ** 2 - 1)) = sin(-x + 3*pi/2)*sin(x - 3*pi)*cos(-x + 2*pi)**2/((2*cos(-x/2 - pi/2)**2 - 1)*sin(-x - pi)*sin(x + pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x - pi) = 2 * cos(-x/2 - pi/2) ** 2 - 1,
{
have : cos(-x - pi) = cos(2*(-x/2 - pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 3*pi/2) = -cos(x),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 3*pi/2) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x - 3*pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x - 3*pi) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 2*pi) = cos(-x),
{
rw cos_eq_cos_add_int_mul_two_pi (-x + 2*pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x - pi) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_185_MACM_extend(h0 : 2 ≠ 0)  : (-cos(-2*pi)*cos(-x + 267*pi/2) - sin(-2*pi)*cos(x + 150*pi))*sin(x - pi/3) + cos(x)*cos(x - pi/3)=1/2:=
begin
have : (-cos(-x + 267 * pi / 2) * cos((-2) * pi) - sin((-2) * pi) * cos(x + 150 * pi)) * sin(x - pi / 3) + cos(x) * cos(x - pi / 3) = (-cos(-2*pi)*cos(-x + 267*pi/2) - sin(-2*pi)*cos(x + 150*pi))*sin(x - pi/3) + cos(x)*cos(x - pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x - 2*pi) = -cos(-x + 267*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x - 2*pi) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(x - 2 * pi) * cos((-2) * pi) - sin((-2) * pi) * cos(x + 150 * pi)) * sin(x - pi / 3) + cos(x) * cos(x - pi / 3) = (sin(x - 2*pi)*cos(-2*pi) - sin(-2*pi)*cos(x + 150*pi))*sin(x - pi/3) + cos(x)*cos(x - pi/3),
{
field_simp at *,
},
have : cos(x - 2*pi) = cos(x + 150*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (x - 2*pi) (76),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(x - 2 * pi) * cos((-2) * pi) - sin((-2) * pi) * cos(x - 2 * pi)) * sin(x - pi / 3) + cos(x) * cos(x - pi / 3) = (sin(x - 2*pi)*cos(-2*pi) - sin(-2*pi)*cos(x - 2*pi))*sin(x - pi/3) + cos(x)*cos(x - pi/3),
{
field_simp at *,
},
have : sin(x) = sin(x - 2*pi) * cos(-2*pi) - sin(-2*pi) * cos(x - 2*pi),
{
have : sin(x) = sin((x - 2*pi) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi/3) = sin(x)*cos(pi/3) - sin(pi/3)*cos(x),
{
have : sin(x-pi/3) = sin((x) - (pi/3)),
{
apply congr_arg,
ring,
},
rw sin_sub,
ring,
},
rw this,
have : cos(x - pi/3) = sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
{
have : cos(x-pi/3) = cos((x) - (pi/3)),
{
apply congr_arg,
ring,
},
rw cos_sub,
ring,
},
rw this,
rw sin_pi_div_three,
rw cos_pi_div_three,
have : cos(x)*(sqrt(3)/2*sin(x) + 1/2*cos(x))= sqrt(3)*sin(x)*cos(x)/2 + cos(x)**2/2,
{
ring_exp,
},
rw this,
have : sin(x)*(sin(x)*(1/2) - sqrt(3)/2*cos(x)) = sin(x)**2/2 - sqrt(3)*sin(x)*cos(x)/2,
{
ring_exp,
},
rw this,
have : sin(x)**2/2 - sqrt(3)*sin(x)*cos(x)/2 + (sqrt(3)*sin(x)*cos(x)/2 + cos(x)**2/2) = sin(x)**2/2 + cos(x)**2/2,
{
ring,
},
rw this,
have : sin(x)**2/2 + cos(x)**2/2 = 1/2,
{
have : sin(x)**2 + cos(x)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
end


lemma Trigo_1_186_IQRK_extend(h0 : cos(3*pi/5) ≤ 0)  : sqrt(1 - cos(691*pi/10)**2)=1 - 2*(1 - 2*sin(3*pi/20)**2)**2:=
begin
have : sqrt (1 - (-cos(691 * pi / 10)) ** 2) = sqrt(1 - cos(691*pi/10)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/5) = -cos(691*pi/10),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (3*pi/5) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/10) = 1 - 2 * sin(3*pi/20) ** 2,
{
have : cos(3*pi/10) = cos(2*(3*pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : -(2 * cos(3 * pi / 10) ** 2 - 1) = 1 - 2*cos(3*pi/10)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(3*pi/5) = 2 * cos(3*pi/10) ** 2 - 1,
{
have : cos(3*pi/5) = cos(2*(3*pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_rhs, rw ← this,},
have : 1 - sin(3*pi/5)**2 = cos(3*pi/5)**2,
{
rw cos_sq',
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h0,
end


lemma Trigo_1_187_TXAZ_extend (h0 : cos(5621*pi/36)≠ 0) (h1 : (2*cos(5621*pi/36))≠ 0) (h2 : sin(5*pi/36)≠ 0) (h3 : (2*sin(5*pi/36))≠ 0) : -sin(pi/9)*sin(5621*pi/18)/(2*cos(5621*pi/36)) + sin(5*pi/18)*sin(7*pi/18)/(2*sin(5*pi/36))=sqrt(2)/2:=
begin
have : -sin(pi / 9) * sin(5621 * pi / 18) / (2 * cos(5621 * pi / 36)) + sin(7 * pi / 18) * (sin(5 * pi / 18) / (2 * sin(5 * pi / 36))) = -sin(pi/9)*sin(5621*pi/18)/(2*cos(5621*pi/36)) + sin(5*pi/18)*sin(7*pi/18)/(2*sin(5*pi/36)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/36) = sin(5*pi/18) / ( 2 * sin(5*pi/36) ),
{
have : sin(5*pi/18) = sin(2*(5*pi/36)),
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
have : -sin(pi / 9) * (sin(5621 * pi / 18) / (2 * cos(5621 * pi / 36))) + sin(7 * pi / 18) * cos(5 * pi / 36) = -sin(pi/9)*sin(5621*pi/18)/(2*cos(5621*pi/36)) + sin(7*pi/18)*cos(5*pi/36),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5621*pi/36) = sin(5621*pi/18) / ( 2 * cos(5621*pi/36) ),
{
have : sin(5621*pi/18) = sin(2*(5621*pi/36)),
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
have : sin(pi / 9) * -sin(5621 * pi / 36) + sin(7 * pi / 18) * cos(5 * pi / 36) = -sin(pi/9)*sin(5621*pi/36) + sin(7*pi/18)*cos(5*pi/36),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(23*pi/36) = -sin(5621*pi/36),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (23*pi/36) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9)*cos(23*pi/36) = -sin(19*pi/36)/2 + sin(3*pi/4)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((23*pi/36) + (pi/9)) = sin(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin((23*pi/36) - (pi/9)) = sin(19*pi/36),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(7*pi/18)*cos(5*pi/36) = sin(pi/4)/2 + sin(19*pi/36)/2,
{
rw sin_mul_cos,
have : sin((7*pi/18) + (5*pi/36)) = sin(19*pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : sin((7*pi/18) - (5*pi/36)) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : -sin(19*pi/36)/2 + sin(3*pi/4)/2 + (sin(pi/4)/2 + sin(19*pi/36)/2) = sin(pi/4)/2 + sin(3*pi/4)/2,
{
ring,
},
rw this,
have : sin(3*pi/4) = sin(pi/4),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
apply congr_arg,
simp,
ring,
},
rw this,
rw sin_pi_div_four,
norm_num,
end


lemma Trigo_1_188_BDYM_extend : -cos(11*pi/6)*cos(2225*pi/12) - sin(-29*pi/6)*cos(25*pi/12)=sqrt(2)/2:=
begin
have : -cos(2225 * pi / 12) * cos(11 * pi / 6) - sin((-29) * pi / 6) * cos(25 * pi / 12) = -cos(11*pi/6)*cos(2225*pi/12) - sin(-29*pi/6)*cos(25*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(25*pi/12) = -cos(2225*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (25*pi/12) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(25 * pi / 12) * cos(11 * pi / 6) + -sin((-29) * pi / 6) * cos(25 * pi / 12) = sin(25*pi/12)*cos(11*pi/6) - sin(-29*pi/6)*cos(25*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1085*pi/6) = -sin(-29*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (1085*pi/6) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(1085 * pi / 6) * cos(25 * pi / 12) + sin(25 * pi / 12) * cos(11 * pi / 6) = sin(25*pi/12)*cos(11*pi/6) + sin(1085*pi/6)*cos(25*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/6) = -sin(1085*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (11*pi/6) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw add_comm,
rw neg_mul,
rw ← sub_eq_add_neg,
have : sin(25*pi/12)*cos(11*pi/6) - sin(11*pi/6)*cos(25*pi/12) = sin(pi/4),
{
have : sin(pi/4) = sin((25*pi/12) - (11*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_four,
end


lemma Trigo_1_189_KEAM_extend (h0 : sin(13951*pi/180)≠ 0) (h1 : (2*sin(13951*pi/180))≠ 0) (h2 : (2*sin(13951*pi/180)**3)≠ 0) : (-sin(13951*pi/90)**3/(2*sin(13951*pi/180)**3) + 3*sin(13951*pi/90)/(2*sin(13951*pi/180)))*cos(pi/15) + cos(pi/60)*cos(13*pi/30)=(sqrt(2)*(sqrt(3)-1))/4:=
begin
have : ((-4) * (sin(13951 * pi / 90) / (2 * sin(13951 * pi / 180))) ** 3 + 3 * (sin(13951 * pi / 90) / (2 * sin(13951 * pi / 180)))) * cos(pi / 15) + cos(pi / 60) * cos(13 * pi / 30) = (-sin(13951*pi/90)**3/(2*sin(13951*pi/180)**3) + 3*sin(13951*pi/90)/(2*sin(13951*pi/180)))*cos(pi/15) + cos(pi/60)*cos(13*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13951*pi/180) = sin(13951*pi/90) / ( 2 * sin(13951*pi/180) ),
{
have : sin(13951*pi/90) = sin(2*(13951*pi/180)),
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
have : ((-4) * cos(13951 * pi / 180) ** 3 + 3 * cos(13951 * pi / 180)) * cos(pi / 15) + cos(pi / 60) * cos(13 * pi / 30) = (-4*cos(13951*pi/180)**3 + 3*cos(13951*pi/180))*cos(pi/15) + cos(pi/60)*cos(13*pi/30),
{
field_simp at *,
},
have : sin(pi/180) = cos(13951*pi/180),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/180) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(pi / 180) ** 3 + 3 * sin(pi / 180)) * cos(pi / 15) + cos(pi / 60) * cos(13 * pi / 30) = (-4*sin(pi/180)**3 + 3*sin(pi/180))*cos(pi/15) + cos(pi/60)*cos(13*pi/30),
{
field_simp at *,
},
have : sin(pi/60) = -4 * sin(pi/180) ** 3 + 3 * sin(pi/180),
{
have : sin(pi/60) = sin(3*(pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(13*pi/30) = sin(pi/15),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/30) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_comm (cos(pi/60)) (sin(pi/15)),
have : sin(pi/60)*cos(pi/15) + sin(pi/15)*cos(pi/60) = sin(pi/12),
{
have : sin(pi/12) = sin((pi/15) + (pi/60)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_twelve,
field_simp,
ring_exp,
rw ← sqrt_mul,
ring,
repeat {linarith},
end


lemma Trigo_1_190_SZEJ_extend(h0 : cos(x) ≠ 0) (h1 : sin(x) ≠ 0) (h2 : (cos(-x-pi)**3*tan(-x-2*pi)*tan(x+pi))≠ 0) : (-4*cos(x/3 + 502*pi/3)**3 + 3*cos(x/3 + 502*pi/3))*cos(-x + 225*pi/2)**2/(cos(-x - pi)**3*tan(-x - 2*pi)*tan(x + pi))=-1:=
begin
have : (4 * (-cos(x / 3 + 502 * pi / 3)) ** 3 - 3 * -cos(x / 3 + 502 * pi / 3)) * cos(-x + 225 * pi / 2) ** 2 / (cos(-x - pi) ** 3 * tan(-x - 2 * pi) * tan(x + pi)) = (-4*cos(x/3 + 502*pi/3)**3 + 3*cos(x/3 + 502*pi/3))*cos(-x + 225*pi/2)**2/(cos(-x - pi)**3*tan(-x - 2*pi)*tan(x + pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x/3 + pi/3) = -cos(x/3 + 502*pi/3),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x/3 + pi/3) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (4 * cos(x / 3 + pi / 3) ** 3 - 3 * cos(x / 3 + pi / 3)) * (-cos(-x + 225 * pi / 2)) ** 2 / (cos(-x - pi) ** 3 * tan(-x - 2 * pi) * tan(x + pi)) = (4*cos(x/3 + pi/3)**3 - 3*cos(x/3 + pi/3))*cos(-x + 225*pi/2)**2/(cos(-x - pi)**3*tan(-x - 2*pi)*tan(x + pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) = -cos(-x + 225*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) ** 2 * (4 * cos(x / 3 + pi / 3) ** 3 - 3 * cos(x / 3 + pi / 3)) / (cos(-x - pi) ** 3 * tan(-x - 2 * pi) * tan(x + pi)) = (4*cos(x/3 + pi/3)**3 - 3*cos(x/3 + pi/3))*sin(x + pi)**2/(cos(-x - pi)**3*tan(-x - 2*pi)*tan(x + pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi) = 4 * cos(x/3 + pi/3) ** 3 - 3 * cos(x/3 + pi/3),
{
have : cos(x + pi) = cos(3*(x/3 + pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x + pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x - pi) = cos(x + pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x - pi) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x + pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-x - 2*pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - 2*pi) (-2),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(x + pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
rw tan_eq_sin_div_cos,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_191_VIFV_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : (sin(-x-pi)*sin(-x+3*pi)*cos(pi-x))≠ 0) (h3 : (((-4)*sin(-x/3-pi/3)**3+3*sin(-x/3-pi/3))*sin(-x+3*pi)*cos(pi-x))≠ 0) (h4 : ((-4*sin(-x/3-pi/3)**3+3*sin(-x/3-pi/3))*sin(-x+3*pi)*cos(pi-x))≠ 0) : (-sin(x/2 + pi/2)**2 + cos(x/2 + pi/2)**2)*cos(x + 61*pi/2)/((-4*sin(-x/3 - pi/3)**3 + 3*sin(-x/3 - pi/3))*sin(-x + 3*pi)*cos(pi - x))=-1/sin(x):=
begin
have : (-sin(x / 2 + pi / 2) ** 2 + cos(x / 2 + pi / 2) ** 2) * cos(x + 61 * pi / 2) / (((-4) * sin(-x / 3 - pi / 3) ** 3 + 3 * sin(-x / 3 - pi / 3)) * sin(-x + 3 * pi) * cos(pi - x)) = (-sin(x/2 + pi/2)**2 + cos(x/2 + pi/2)**2)*cos(x + 61*pi/2)/((-4*sin(-x/3 - pi/3)**3 + 3*sin(-x/3 - pi/3))*sin(-x + 3*pi)*cos(pi - x)),
{
field_simp at *,
},
have : sin(-x + 2*pi) = cos(x + 61*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x + 2*pi) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(x / 2 + pi / 2) ** 2 + cos(x / 2 + pi / 2) ** 2) * sin(-x + 2 * pi) / (((-4) * sin(-x / 3 - pi / 3) ** 3 + 3 * sin(-x / 3 - pi / 3)) * sin(-x + 3 * pi) * cos(pi - x)) = (-sin(x/2 + pi/2)**2 + cos(x/2 + pi/2)**2)*sin(-x + 2*pi)/((-4*sin(-x/3 - pi/3)**3 + 3*sin(-x/3 - pi/3))*sin(-x + 3*pi)*cos(pi - x)),
{
field_simp at *,
},
have : sin(-x - pi) = -4 * sin(-x/3 - pi/3) ** 3 + 3 * sin(-x/3 - pi/3),
{
have : sin(-x - pi) = sin(3*(-x/3 - pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2 * pi) * (-sin(x / 2 + pi / 2) ** 2 + cos(x / 2 + pi / 2) ** 2) / (sin(-x - pi) * sin(-x + 3 * pi) * cos(pi - x)) = (-sin(x/2 + pi/2)**2 + cos(x/2 + pi/2)**2)*sin(-x + 2*pi)/(sin(-x - pi)*sin(-x + 3*pi)*cos(pi - x)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi) = -sin(x/2 + pi/2) ** 2 + cos(x/2 + pi/2) ** 2,
{
have : cos(x + pi) = cos(2*(x/2 + pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2*pi) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x + 3*pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x + 3*pi) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi - x) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_192_NTYS_extend : 2 - (-2*sin(35*pi/8)**2 + 1 + sqrt(3)*cos(623*pi/4))**2=sqrt(3):=
begin
have : 2 - ((-2) * sin(35 * pi / 8) ** 2 + 1 + sqrt 3 * cos(623 * pi / 4)) ** 2 = 2 - (-2*sin(35*pi/8)**2 + 1 + sqrt(3)*cos(623*pi/4))**2,
{
field_simp at *,
},
have : cos(pi/8) = sin(35*pi/8),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/8) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 - (-(2 * cos(pi / 8) ** 2 - 1) + sqrt 3 * cos(623 * pi / 4)) ** 2 = 2 - (-2*cos(pi/8)**2 + 1 + sqrt(3)*cos(623*pi/4))**2,
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
have : 2 - (sqrt 3 * cos(623 * pi / 4) - cos(pi / 4)) ** 2 = 2 - (-cos(pi/4) + sqrt(3)*cos(623*pi/4))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = cos(623*pi/4),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/4) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw cos_pi_div_four,
rw sin_pi_div_four,
ring_exp,
repeat {rw sq_sqrt},
ring,
repeat {linarith},
end


lemma Trigo_1_193_QDVP_extend : -1 + 2*(-6*sin(1943*pi/48)**2 + 3 + 4*(-1 + 2*sin(1943*pi/48)**2)**3)**2=sqrt(2)/2:=
begin
have : -1 + 2 * ((-6) * sin(1943 * pi / 48) ** 2 + 3 + 4 * (-1 + 2 * sin(1943 * pi / 48) ** 2) ** 3) ** 2 = -1 + 2*(-6*sin(1943*pi/48)**2 + 3 + 4*(-1 + 2*sin(1943*pi/48)**2)**3)**2,
{
field_simp at *,
},
have : cos(pi/48) = sin(1943*pi/48),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/48) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -1 + 2 * ((-3) * (2 * cos(pi / 48) ** 2 - 1) + 4 * (2 * cos(pi / 48) ** 2 - 1) ** 3) ** 2 = -1 + 2*(-6*cos(pi/48)**2 + 3 + 4*(-1 + 2*cos(pi/48)**2)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = 2 * cos(pi/48) ** 2 - 1,
{
have : cos(pi/24) = cos(2*(pi/48)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : 2 * (4 * cos(pi / 24) ** 3 - 3 * cos(pi / 24)) ** 2 - 1 = -1 + 2*(-3*cos(pi/24) + 4*cos(pi/24)**3)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
conv {to_lhs, rw ← this,},
have : 2*cos(pi/8)**2 - 1 = cos(pi/4),
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
rw cos_pi_div_four,
end


lemma Trigo_1_194_PAUS_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : (sin(-x-pi)*sin(-x+3*pi)*sin(x+9*pi/2)*cos(pi-x))≠ 0) (h3 : (sin(-x-pi)*sin(-x+43*pi)*sin(x+9*pi/2)*cos(pi-x))≠ 0) (h4 : ((sin(-x-5*pi/6)*cos(-pi/6)+sin(-pi/6)*cos(-x-5*pi/6))*sin(-x+43*pi)*sin(x+9*pi/2)*cos(pi-x))≠ 0) : -cos(-x + 5*pi/2)*cos(-x + 11*pi/2)*cos(x + pi)/((sin(-x - 5*pi/6)*cos(-pi/6) + sin(-pi/6)*cos(-x - 5*pi/6))*sin(-x + 43*pi)*sin(x + 9*pi/2)*cos(pi - x))=1/cos(x):=
begin
have : sin(-x - pi) = sin(-x - 5*pi/6) * cos(-pi/6) + sin(-pi/6) * cos(-x - 5*pi/6),
{
have : sin(-x - pi) = sin((-x - 5*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 3*pi) = sin(-x + 43*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (-x + 3*pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2*pi) = -cos(-x + 5*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-x + 2*pi) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2*pi) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 11*pi/2) = -sin(x),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 11*pi/2) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi - x) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x + 3*pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x + 3*pi) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + 9*pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 9*pi/2) (-3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
end


lemma Trigo_1_195_TRHQ_extend(h0 : sin(pi/18) ≥ 0) (h1 : -cos(pi/18) + sin(pi/18) ≤ 0) (h2 : -sin(pi/18) + cos(pi/18) ≠ 0)  (h3 : (-sqrt(1-(-sin(10*pi/9)*sin(-pi/6)+cos(10*pi/9)*cos(-pi/6))**2)+cos(pi/18))≠ 0) (h4 : (-sqrt(1-(cos(-pi/6)*cos(10*pi/9)-sin(-pi/6)*sin(10*pi/9))**2)+cos(pi/18))≠ 0) (h5 : (-sqrt(1-(cos(-pi/6)*cos(10*pi/9)-cos(116*pi/3)*sin(10*pi/9))**2)+cos(pi/18))≠ 0) (h6 : (-sqrt(1-(cos(-pi/6)*cos(10*pi/9)-sin(10*pi/9)*cos(116*pi/3))**2)+cos(pi/18))≠ 0) (h7 : (-sqrt(1-(sin(494*pi/3)*cos(10*pi/9)-sin(10*pi/9)*cos(116*pi/3))**2)+cos(pi/18))≠ 0) : sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - (sin(494*pi/3)*cos(10*pi/9) - sin(10*pi/9)*cos(116*pi/3))**2) + cos(pi/18))=1:=
begin
have : sqrt ((-2) * sin(pi / 18) * cos(pi / 18) + 1) / (-sqrt (1 - (sin(494 * pi / 3) * cos(10 * pi / 9) - sin(10 * pi / 9) * cos(116 * pi / 3)) ** 2) + cos(pi / 18)) = sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - (sin(494*pi/3)*cos(10*pi/9) - sin(10*pi/9)*cos(116*pi/3))**2) + cos(pi/18)),
{
field_simp at *,
},
have : cos(-pi/6) = sin(494*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * cos(pi / 18) + 1) / (-sqrt (1 - (cos(-pi / 6) * cos(10 * pi / 9) - cos(116 * pi / 3) * sin(10 * pi / 9)) ** 2) + cos(pi / 18)) = sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - (cos(-pi/6)*cos(10*pi/9) - sin(10*pi/9)*cos(116*pi/3))**2) + cos(pi/18)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/6) = cos(116*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-pi/6) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * cos(pi / 18) + 1) / (-sqrt (1 - (-sin(10 * pi / 9) * sin(-pi / 6) + cos(10 * pi / 9) * cos(-pi / 6)) ** 2) + cos(pi / 18)) = sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - (cos(-pi/6)*cos(10*pi/9) - sin(-pi/6)*sin(10*pi/9))**2) + cos(pi/18)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/18) = -sin(10*pi/9) * sin(-pi/6) + cos(10*pi/9) * cos(-pi/6),
{
have : cos(17*pi/18) = cos((10*pi/9) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(17*pi/18)**2 = sin(17*pi/18)**2,
{
rw sin_sq,
},
rw this,
have : sin(17*pi/18) = sin(pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
have : -2*sin(pi/18)*cos(pi/18) + 1 = -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2,
{
rw add_assoc,
rw sin_sq_add_cos_sq,
},
rw this,
have : -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 = (-cos(pi/18) + sin(pi/18))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h1,
field_simp,
end


lemma Trigo_1_196_IFKW_extend (h0 : sin(-x + 11*pi/18)≠ 0) (h1 : (2*sin(-x+11*pi/18))≠ 0) : sin(-2*x + 11*pi/9)*cos(x + 2435*pi/36)/(2*sin(-x + 11*pi/18)) - sin(-x + 13*pi/36)*cos(x + 242*pi/9)=sqrt(2)/2:=
begin
have : sin((-2) * x + 11 * pi / 9) * cos(x + 2435 * pi / 36) / (2 * sin(-x + 11 * pi / 18)) - sin(-x + 13 * pi / 36) * cos(x + 242 * pi / 9) = sin(-2*x + 11*pi/9)*cos(x + 2435*pi/36)/(2*sin(-x + 11*pi/18)) - sin(-x + 13*pi/36)*cos(x + 242*pi/9),
{
field_simp at *,
},
have : cos(-x + 13*pi/36) = cos(x + 2435*pi/36),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 13*pi/36) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-2) * x + 11 * pi / 9) * cos(-x + 13 * pi / 36) / (2 * sin(-x + 11 * pi / 18)) + sin(-x + 13 * pi / 36) * -cos(x + 242 * pi / 9) = sin(-2*x + 11*pi/9)*cos(-x + 13*pi/36)/(2*sin(-x + 11*pi/18)) - sin(-x + 13*pi/36)*cos(x + 242*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi/9) = -cos(x + 242*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x - pi/9) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 13 * pi / 36) * cos(x - pi / 9) + cos(-x + 13 * pi / 36) * (sin((-2) * x + 11 * pi / 9) / (2 * sin(-x + 11 * pi / 18))) = sin(-2*x + 11*pi/9)*cos(-x + 13*pi/36)/(2*sin(-x + 11*pi/18)) + sin(-x + 13*pi/36)*cos(x - pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 11*pi/18) = sin(-2*x + 11*pi/9) / ( 2 * sin(-x + 11*pi/18) ),
{
have : sin(-2*x + 11*pi/9) = sin(2*(-x + 11*pi/18)),
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
have : cos(-x + 11*pi/18) = sin(x - pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + 11*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_comm (cos(-x + 13*pi/36)) (sin(x - pi/9)),
have : sin(-x + 13*pi/36)*cos(x - pi/9) + sin(x - pi/9)*cos(-x + 13*pi/36) = sin(pi/4),
{
have : sin(pi/4) = sin((x - pi/9) + (-x + 13*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add (x - pi/9) (-x + 13*pi/36),
ring,
},
rw this,
rw sin_pi_div_four,
end


lemma Trigo_1_197_ZSYQ_extend(h0 : sin(5*pi/18) ≠ 0) (h1 : cos(2*pi/9)≠ 0) (h2 : sin(2075*pi/18)≠ 0) (h3 : -sin(2075*pi/18)≠ 0) : (sin(703*pi/18) + sqrt(3)*cos(2881*pi/18))/sin(2075*pi/18)=-2:=
begin
have : -(-sqrt 3 * cos(2881 * pi / 18) + -sin(703 * pi / 18)) / sin(2075 * pi / 18) = (sin(703*pi/18) + sqrt(3)*cos(2881*pi/18))/sin(2075*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = -sin(703*pi/18),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/18) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sqrt 3 * cos(2881 * pi / 18) + sin(pi / 18)) / -sin(2075 * pi / 18) = -(-sqrt(3)*cos(2881*pi/18) + sin(pi/18))/sin(2075*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = -sin(2075*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/9) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 18) - sqrt 3 * cos(2881 * pi / 18)) / cos(2 * pi / 9) = (-sqrt(3)*cos(2881*pi/18) + sin(pi/18))/cos(2*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = cos(2881*pi/18),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/18) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3)*cos(pi/18) = 2*sin(pi/3)*cos(pi/18),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/18) = 2*sin(pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
rw sub_eq_neg_add,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/3)*cos(pi/18) + 2*sin(pi/18)*cos(pi/3) = 2*sin(-5*pi/18),
{
have : sin(-5*pi/18) = sin(pi/18)*cos(pi/3) - sin(pi/3)*cos(pi/18),
{
have : sin(-5*pi/18) = sin((pi/18) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : cos(2*pi/9) = sin(5*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-5*pi/18) = -sin(5*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
end


lemma Trigo_1_198_UYVG_extend : (-1 + 2*cos(7*pi/18)**2)*sin(1126*pi/9) + sin(2*pi/9)*sin(587*pi/18)=sqrt(3)/2:=
begin
have : sin(1126 * pi / 9) * (2 * cos(7 * pi / 18) ** 2 - 1) + sin(2 * pi / 9) * sin(587 * pi / 18) = (-1 + 2*cos(7*pi/18)**2)*sin(1126*pi/9) + sin(2*pi/9)*sin(587*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/9) = 2 * cos(7*pi/18) ** 2 - 1,
{
have : cos(7*pi/9) = cos(2*(7*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(1126 * pi / 9) * cos(7 * pi / 9) - sin(2 * pi / 9) * -sin(587 * pi / 18) = sin(1126*pi/9)*cos(7*pi/9) + sin(2*pi/9)*sin(587*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(8*pi/9) = -sin(587*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/9) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(2 * pi / 9) * cos(8 * pi / 9) + sin(1126 * pi / 9) * cos(7 * pi / 9) = sin(1126*pi/9)*cos(7*pi/9) - sin(2*pi/9)*cos(8*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(10*pi/9) = sin(1126*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (10*pi/9) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw neg_mul,
have : sin(2*pi/9)*cos(8*pi/9) = -sin(2*pi/3)/2 + sin(10*pi/9)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((8*pi/9) + (2*pi/9)) = sin(10*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((8*pi/9) - (2*pi/9)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(10*pi/9)*cos(7*pi/9) = sin(17*pi/9)/2 + sin(pi/3)/2,
{
rw sin_mul_cos,
have : sin((10*pi/9) + (7*pi/9)) = sin(17*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((10*pi/9) - (7*pi/9)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(17*pi/9) = -sin(8*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (17*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/3) = sin(2*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(10*pi/9) = -sin(pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (10*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_two_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_1_199_EXFT_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : cos(2*x) ≠ 0)  (h3 : (sin(2*x)*sin(-2*x+93*pi/2))≠ 0) (h4 : (sin(2*x)*sin((-2)*x+93*pi/2))≠ 0) (h5 : cos((4*x)/2)≠ 0) (h6 : (1+cos(4*x))≠ 0) (h7 : (cos(4*x)+1)≠ 0) : (2 - 2*sin(-2*x + 93*pi/2))*cos(-x + 5*pi)**2/(sin(2*x)*sin(-2*x + 93*pi/2))=sin(4*x)/(cos(4*x) + 1):=
begin
have : sin(4 * x) / (1 + cos(4 * x)) = sin(4*x)/(cos(4*x) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : tan(2*x) = sin(4*x) / ( 1 + cos(4*x) ),
{
have : tan(2*x) = tan((4*x)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : (2 - 2 * sin((-2) * x + 93 * pi / 2)) * (-cos(-x + 5 * pi)) ** 2 / (sin(2 * x) * sin((-2) * x + 93 * pi / 2)) = (2 - 2*sin(-2*x + 93*pi/2))*cos(-x + 5*pi)**2/(sin(2*x)*sin(-2*x + 93*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -cos(-x + 5*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (x) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (1 - sin((-2) * x + 93 * pi / 2)) * cos(x) ** 2 / (sin(2 * x) * sin((-2) * x + 93 * pi / 2)) = (2 - 2*sin(-2*x + 93*pi/2))*cos(x)**2/(sin(2*x)*sin(-2*x + 93*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = sin(-2*x + 93*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*x) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(2*x) = 2*sin(x)**2,
{
have : sin(x)**2 = 1/2 - cos(2*x)/2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
ring,
},
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_200_VKFM_extend(h0 : cos (pi/8) ≠ 0)  (h2 : tan(201*pi/8)≠ 0) (h3 : cos(201*pi/8)≠ 0) (h4 : sin(201*pi/8)≠ 0) (h5 : (sin(201*pi/8)/cos(201*pi/8))≠ 0) (h6 : sin(201*pi/8)≠ 0) (h7 : (2*sin(201*pi/8))≠ 0) (h8 : (2*sin(201*pi/8)**2)≠ 0) : sin(201*pi/4)/(2*sin(201*pi/8)**2)=1+sqrt(2):=
begin
have : sin(201 * pi / 4) / (2 * sin(201 * pi / 8)) / sin(201 * pi / 8) = sin(201*pi/4)/(2*sin(201*pi/8)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(201*pi/8) = sin(201*pi/4) / ( 2 * sin(201*pi/8) ),
{
have : sin(201*pi/4) = sin(2*(201*pi/8)),
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
have : 1 / (sin(201 * pi / 8) / cos(201 * pi / 8)) = cos(201*pi/8)/sin(201*pi/8),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(201*pi/8) = sin(201*pi/8) / cos(201*pi/8),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = tan(201*pi/8),
{
rw tan_eq_tan_add_int_mul_pi (pi/8) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = sin(pi/4)/(1+ cos(pi/4)),
{
have : cos(pi/8) = cos((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this at *,
have : tan(pi/8) = tan((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_201_HEEI_extend : cos(491*pi/15)/2 + sin(pi/6)/2 + (-sin(pi)*cos(6*pi/5) + sin(6*pi/5)*cos(pi))*cos(pi/30)=1/2:=
begin
have : cos(491 * pi / 15) / 2 + sin(pi / 6) / 2 + (sin(6 * pi / 5) * cos(pi) - sin(pi) * cos(6 * pi / 5)) * cos(pi / 30) = cos(491*pi/15)/2 + sin(pi/6)/2 + (-sin(pi)*cos(6*pi/5) + sin(6*pi/5)*cos(pi))*cos(pi/30),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5) = sin(6*pi/5) * cos(pi) - sin(pi) * cos(6*pi/5),
{
have : sin(pi/5) = sin((6*pi/5) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : - -cos(491 * pi / 15) / 2 + sin(pi / 6) / 2 + sin(pi / 5) * cos(pi / 30) = cos(491*pi/15)/2 + sin(pi/6)/2 + sin(pi/5)*cos(pi/30),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/30) = -cos(491*pi/15),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (23*pi/30) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 5) * cos(pi / 30) - (-sin(pi / 6) / 2 + sin(23 * pi / 30) / 2) = -sin(23*pi/30)/2 + sin(pi/6)/2 + sin(pi/5)*cos(pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/10) * cos(7*pi/15) = -sin(pi/6) / 2 + sin(23*pi/30) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((7*pi/15) + (3*pi/10)) = sin(23*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((7*pi/15) - (3*pi/10)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(3*pi/10) * cos(7*pi/15)) = sin(3*pi/10)*cos(7*pi/15),
{
ring,
},
have : sin(3*pi/10)*cos(7*pi/15) = -sin(pi/6)/2 + sin(23*pi/30)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((7*pi/15) + (3*pi/10)) = sin(23*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((7*pi/15) - (3*pi/10)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(pi/5)*cos(pi/30) = sin(pi/6)/2 + sin(7*pi/30)/2,
{
rw sin_mul_cos,
have : sin((pi/5) + (pi/30)) = sin(7*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/5) - (pi/30)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(7*pi/30) = sin(23*pi/30),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/30) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_2_202_GVCN_extend : -sqrt(3)*sin(x)/2 + sin(x - 211*pi/2)/2=sin(-x+pi/6):=
begin
have : -sqrt 3 * sin(x) / 2 - -sin(x - 211 * pi / 2) / 2 = -sqrt(3)*sin(x)/2 + sin(x - 211*pi/2)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 383*pi/2) = -sin(x - 211*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 383*pi/2) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * sin(x) / 2 - sin(-x + 383 * pi / 2) / 2 = -sqrt(3)*sin(x)/2 - sin(-x + 383*pi/2)/2,
{
field_simp at *,
},
have : cos(-x + 185*pi) = sin(-x + 383*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-x + 185*pi) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * sin(x) / 2 + -cos(-x + 185 * pi) / 2 = -sqrt(3)*sin(x)/2 - cos(-x + 185*pi)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -cos(-x + 185*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (x) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt(3)*sin(x)/2 = -sin(x)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(x)/2 = sin(pi/6)*cos(x),
{
field_simp,
},
rw this,
have : -sin(x)*cos(pi/6) + sin(pi/6)*cos(x) = sin(-x + pi/6),
{
have : sin(-x+pi/6) = sin((pi/6) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
end


lemma Trigo_2_203_KQQP_extend(h0 : 2 - cos(pi/18)**2 ≠ 0)  (h1 : (2-cos(pi/18)**2)≠ 0) (h2 : (2-cos(1945*pi/18)**2)≠ 0) : (2*(-4*sin(pi/54)**3 + 3*sin(pi/54))**2 + 2)/(2 - cos(1945*pi/18)**2)=2:=
begin
have : (2 * ((-4) * sin(pi / 54) ** 3 + 3 * sin(pi / 54)) ** 2 + 2) / (2 - cos(1945 * pi / 18) ** 2) = (2*(-4*sin(pi/54)**3 + 3*sin(pi/54))**2 + 2)/(2 - cos(1945*pi/18)**2),
{
field_simp at *,
},
have : cos(pi/18) = cos(1945*pi/18),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/18) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * ((-4) * sin(pi / 54) ** 3 + 3 * sin(pi / 54)) ** 2 + 2) / (2 - cos(pi / 18) ** 2) = (2*(-4*sin(pi/54)**3 + 3*sin(pi/54))**2 + 2)/(2 - cos(pi/18)**2),
{
field_simp at *,
},
have : sin(pi/18) = -4 * sin(pi/54) ** 3 + 3 * sin(pi/54),
{
have : sin(pi/18) = sin(3*(pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (3 - (1 - 2 * sin(pi / 18) ** 2)) / (2 - cos(pi / 18) ** 2) = (2*sin(pi/18)**2 + 2)/(2 - cos(pi/18)**2),
{
field_simp at *,
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
have : cos(pi/9) = -1 + 2*cos(pi/18)**2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
have : 3 - (-1 + 2 * cos(pi / 18) ** 2) = 4 - 2*cos(pi/18)**2,
{
ring,
},
rw this,
have : (4 - 2*cos(pi/18)**2)/(2 - cos(pi/18)**2) = 2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
end


lemma Trigo_2_204_FKBX_extend(h0 : cos(x) ≠ 0) (h1 : cos(2*x) ≠ 0) (h2 : ((-sin(x)**2+cos(x)**2+1)*(-sin(x)**2+cos(x)**2))≠ 0) (h3 : ((-sin(x)**2+cos(x)**2)*(-sin(x)**2+cos(x)**2+1))≠ 0) (h4 : ((-(sin(x-pi/2)*cos(-pi/2)-sin(-pi/2)*cos(x-pi/2))**2+cos(x)**2)*(-(sin(x-pi/2)*cos(-pi/2)-sin(-pi/2)*cos(x-pi/2))**2+cos(x)**2+1))≠ 0) (h5 : ((-(sin(x)/2+sin(x-pi)/2-sin(-pi/2)*cos(x-pi/2))**2+cos(x)**2)*(-(sin(x)/2+sin(x-pi)/2-sin(-pi/2)*cos(x-pi/2))**2+cos(x)**2+1))≠ 0) : 2*sin(2*x)*cos(x)**2/((-(sin(x)/2 + sin(x - pi)/2 - sin(-pi/2)*cos(x - pi/2))**2 + cos(x)**2)*(-(sin(x)/2 + sin(x - pi)/2 - sin(-pi/2)*cos(x - pi/2))**2 + cos(x)**2 + 1))=tan(2*x):=
begin
have : sin(x - pi/2) * cos(-pi/2) = sin(x) / 2 + sin(x - pi) / 2,
{
rw sin_mul_cos,
have : sin((x - pi/2) + (-pi/2)) = sin(x - pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((x - pi/2) - (-pi/2)) = sin(x),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(x - pi/2) * cos(-pi/2)) = sin(x-pi/2)*cos(-pi/2),
{
ring,
},
have : sin(x) = sin(x - pi/2) * cos(-pi/2) - sin(-pi/2) * cos(x - pi/2),
{
have : sin(x) = sin((x - pi/2) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(2 * x) * cos(x) ** 2 / ((-sin(x) ** 2 + cos(x) ** 2 + 1) * (-sin(x) ** 2 + cos(x) ** 2)) = 2*sin(2*x)*cos(x)**2/((-sin(x)**2 + cos(x)**2)*(-sin(x)**2 + cos(x)**2 + 1)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -sin(x) ** 2 + cos(x) ** 2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have :cos(2*x) + 1 = 2*cos(x)**2 ,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring_exp,
end


lemma Trigo_2_205_KSQU_extend : sqrt(-2*cos(-518*pi/9)**3 + 3*cos(-518*pi/9)/2 + 1/2)=sqrt(3)/2:=
begin
have : sqrt (2 * (-cos((-518) * pi / 9)) ** 3 - 3 * -cos((-518) * pi / 9) / 2 + 1 / 2) = sqrt(-2*cos(-518*pi/9)**3 + 3*cos(-518*pi/9)/2 + 1/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1063*pi/18) = -cos(-518*pi/9),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1063*pi/18) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (1 / 2 - ((-4) * sin(1063 * pi / 18) ** 3 + 3 * sin(1063 * pi / 18)) / 2) = sqrt(2*sin(1063*pi/18)**3 - 3*sin(1063*pi/18)/2 + 1/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1063*pi/6) = -4 * sin(1063*pi/18) ** 3 + 3 * sin(1063*pi/18),
{
have : sin(1063*pi/6) = sin(3*(1063*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (-sin(1063 * pi / 6) / 2 + 1 / 2) = sqrt(1/2 - sin(1063*pi/6)/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/3) = -sin(1063*pi/6),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/3) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw cos_pi_div_three,
norm_num,
have : sqrt 4 = sqrt (2*2),
{
apply congr_arg,
ring,
},
rw this,
rw sqrt_mul_self,
repeat {linarith},
end


lemma Trigo_2_206_KNLG_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (sin(-x-pi)*sin(-x+3*pi)*sin(x+9*pi/2)*cos(pi-x))≠ 0) : (-sin(-x/2 + 11*pi/4)**2 + cos(-x + 11*pi/2)/2 + 1/2)*sin(-x + 2*pi)*cos(x + pi/2)*cos(x + pi)/(sin(-x - pi)*sin(-x + 3*pi)*sin(x + 9*pi/2)*cos(pi - x))=-tan(x + 88*pi):=
begin
have : (-sin(-x / 2 + 11 * pi / 4) ** 2 + (cos(-x + 11 * pi / 2) / 2 + 1 / 2)) * sin(-x + 2 * pi) * cos(x + pi / 2) * cos(x + pi) / (sin(-x - pi) * sin(-x + 3 * pi) * sin(x + 9 * pi / 2) * cos(pi - x)) = (-sin(-x/2 + 11*pi/4)**2 + cos(-x + 11*pi/2)/2 + 1/2)*sin(-x + 2*pi)*cos(x + pi/2)*cos(x + pi)/(sin(-x - pi)*sin(-x + 3*pi)*sin(x + 9*pi/2)*cos(pi - x)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x/2 + 11*pi/4) ** 2 = cos(-x + 11*pi/2) / 2 + 1 / 2,
{
have : cos(-x + 11*pi/2) = cos(2*(-x/2 + 11*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2 * pi) * (-sin(-x / 2 + 11 * pi / 4) ** 2 + cos(-x / 2 + 11 * pi / 4) ** 2) * cos(x + pi / 2) * cos(x + pi) / (sin(-x - pi) * sin(-x + 3 * pi) * sin(x + 9 * pi / 2) * cos(pi - x)) = (-sin(-x/2 + 11*pi/4)**2 + cos(-x/2 + 11*pi/4)**2)*sin(-x + 2*pi)*cos(x + pi/2)*cos(x + pi)/(sin(-x - pi)*sin(-x + 3*pi)*sin(x + 9*pi/2)*cos(pi - x)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 11*pi/2) = -sin(-x/2 + 11*pi/4) ** 2 + cos(-x/2 + 11*pi/4) ** 2,
{
have : cos(-x + 11*pi/2) = cos(2*(-x/2 + 11*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x) = tan(x + 88*pi),
{
rw tan_eq_tan_add_int_mul_pi (x) (88),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_rhs, rw ← this,},
have : sin(-x + 2*pi) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 11*pi/2) = -sin(x),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 11*pi/2) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x + pi/2) = -sin(x),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x + pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x + 3*pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x + 3*pi) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + 9*pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 9*pi/2) (-3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi - x) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
rw tan_eq_sin_div_cos,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_207_FKOY_extend (h0 : cos(5*pi/12)≠ 0) (h1 : (2*cos(5*pi/12))≠ 0) (h2 : (2*cos(5*pi/12)**2)≠ 0) : -sin(1291*pi/6)**2/(2*cos(5*pi/12)**2) + 1=-sqrt(3)/2:=
begin
have : -(-sin(1291 * pi / 6)) ** 2 / (2 * cos(5 * pi / 12) ** 2) + 1 = -sin(1291*pi/6)**2/(2*cos(5*pi/12)**2) + 1,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(493*pi/6) = -sin(1291*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (493*pi/6) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = sin(493*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (sin(5 * pi / 6) / (2 * cos(5 * pi / 12))) ** 2 = -sin(5*pi/6)**2/(2*cos(5*pi/12)**2) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = sin(5*pi/6) / ( 2 * cos(5*pi/12) ),
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
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_twelve,
field_simp,
ring_exp,
rw sq_sqrt,
norm_num,
rw ← mul_assoc,
rw ← sqrt_mul,
have : sqrt(2*6) = sqrt(3) * sqrt(2*2),
{
rw ← sqrt_mul,
apply congr_arg,
norm_num,
repeat {linarith},
},
rw this,
rw sqrt_mul_self,
ring,
repeat {linarith},
end


lemma Trigo_2_208_GHHR_extend(h0 : sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : sin(pi/9) ≠ 0)  (h3 : sin(1291*pi/9)≠ 0) (h4 : -sin(1291*pi/9)≠ 0) (h5 : sin(17*pi/18)≠ 0) (h6 : cos(1471*pi/9)≠ 0) (h7 : -cos(1471*pi/9)≠ 0) (h8 : cos(2263*pi/9)≠ 0) : 1/cos(2263*pi/9) - sqrt(3)/sin(1291*pi/9)=-4:=
begin
have : 1 / cos(2263 * pi / 9) - sqrt 3 / sin(1291 * pi / 9) = 1/cos(2263*pi/9) - sqrt(3)/sin(1291*pi/9),
{
field_simp at *,
},
have : cos(1471*pi/9) = cos(2263*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (1471*pi/9) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1) / -cos(1471 * pi / 9) - sqrt 3 / sin(1291 * pi / 9) = 1/cos(1471*pi/9) - sqrt(3)/sin(1291*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/18) = -cos(1471*pi/9),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (17*pi/18) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 / -sin(1291 * pi / 9) - 1 / sin(17 * pi / 18) = -1/sin(17*pi/18) - sqrt(3)/sin(1291*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = -sin(1291*pi/9),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/18) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/18) = sin(pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sqrt(3)/cos(pi/18) - 1/sin(pi/18) = (-cos(pi/18) + sqrt(3)*sin(pi/18))/(sin(pi/18)*cos(pi/18)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sin(pi/18)*cos(pi/18) = sin(pi/9)/2,
{
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/6)*cos(pi/18) + 2*sin(pi/18)*cos(pi/6) = 2*sin(-pi/9),
{
have : sin(-pi/9) = sin(pi/18)*cos(pi/6) - sin(pi/6)*cos(pi/18),
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
linarith,
},
rw this,
have : sin(-pi/9) = -sin(pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_209_RURS_extend(h0 : cos (x) ≠ 0)  (h2 : sin(-x+121*pi/2)≠ 0) (h3 : cos(x-46*pi)≠ 0) : (-sin(x + pi/6) - sin(x + 773*pi/6))/cos(x - 46*pi)=-1:=
begin
have : (-sin(x + 773 * pi / 6) - sin(x + pi / 6)) / cos(x - 46 * pi) = (-sin(x + pi/6) - sin(x + 773*pi/6))/cos(x - 46*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi/6) = -sin(x + 773*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x - pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 121*pi/2) = cos(x - 46*pi),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x + 121*pi/2) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(-x + 121*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (x) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi/6) - sin(x + pi/6) = -2*sin(pi/6)*cos(x),
{
have : -sin(x - pi/6) + sin(x + pi/6) = 2*sin(pi/6)*cos(x),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((x + pi/6) + (x - pi/6))/2) = cos(x),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((x + pi/6) - (x - pi/6))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : -2*sin(pi/6) = -1,
{
have : sin(pi/6) = 1/2,
{
rw sin_pi_div_six,
},
linarith,
},
rw this,
norm_num,
field_simp,
end


lemma Trigo_2_210_THJQ_extend(h0 : cos(pi/9) ≥ 0)  : sqrt(1 - sin(-1153*pi/9)**2)=sin(83*pi/18):=
begin
have : sqrt (1 - sin((-1153) * pi / 9) ** 2) = sqrt(1 - sin(-1153*pi/9)**2),
{
field_simp at *,
},
have : cos(3359*pi/18) = sin(-1153*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3359*pi/18) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (1 - (-cos(3359 * pi / 18)) ** 2) = sqrt(1 - cos(3359*pi/18)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(8*pi/9) = -cos(3359*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/9) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(83 * pi / 18) = sin(83*pi/18),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(8*pi/9) = -sin(83*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (8*pi/9) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(8*pi/9) = -cos(pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw ← cos_sq',
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
norm_num,
end


lemma Trigo_2_211_UWCA_extend(h0 : cos(x) ≠ 0) (h1 : (2*cos(x))≠ 0) (h2 : (2*(-sin(x/2)**2+cos(x/2)**2))≠ 0) : (-sin(x + 719*pi/6) - sin(x + 907*pi/6))/(2*(-sin(x/2)**2 + cos(x/2)**2))=1/2:=
begin
have : cos(x) = -sin(x/2) ** 2 + cos(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(x + 907 * pi / 6) - sin(x + 719 * pi / 6)) / (2 * cos(x)) = (-sin(x + 719*pi/6) - sin(x + 907*pi/6))/(2*cos(x)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/6) = -sin(x + 907*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi/6) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(x + pi / 6) + -sin(x + 719 * pi / 6)) / (2 * cos(x)) = (sin(x + pi/6) - sin(x + 719*pi/6))/(2*cos(x)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi/3) = -sin(x + 719*pi/6),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/3) (59),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/6) = cos(-x + pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (x + pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + pi/3) = sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
{
have : cos(-x+pi/3) = cos((pi/3) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw this,
have : cos(x + pi/3) = -sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
{
have : cos(x+pi/3) = cos((x) + (pi/3)),
{
apply congr_arg,
ring,
},
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_212_CWPH_extend (h0 : cos(pi/12)≠ 0) : -sqrt(3)*(cos(-1039*pi/12)/cos(pi/12) + 1) - cos(-1039*pi/12)/cos(pi/12) + 1=0:=
begin
have : -sqrt 3 * (- -cos((-1039) * pi / 12) / cos(pi / 12) + 1) + -cos((-1039) * pi / 12) / cos(pi / 12) + 1 = -sqrt(3)*(cos(-1039*pi/12)/cos(pi/12) + 1) - cos(-1039*pi/12)/cos(pi/12) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1897*pi/12) = -cos(-1039*pi/12),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1897*pi/12) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * (-sin(1897 * pi / 12) / cos(pi / 12) + 1) + sin(1897 * pi / 12) / cos(pi / 12) + 1 = -sqrt(3)*(-sin(1897*pi/12)/cos(pi/12) + 1) + sin(1897*pi/12)/cos(pi/12) + 1,
{
field_simp at *,
},
have : sin(pi/12) = sin(1897*pi/12),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/12) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) / cos(pi / 12) + 1 - sqrt 3 * (1 - sin(pi / 12) / cos(pi / 12)) = -sqrt(3)*(-sin(pi/12)/cos(pi/12) + 1) + sin(pi/12)/cos(pi/12) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = sin(pi/12) / cos(pi/12),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
rw tan_pi_div_twelve,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_213_WZGF_extend(h0 : 2 ≠ 0) (h1 : 4 ≠ 0)  : (-sin(pi)*sin(1285*pi/9) + cos(pi)*cos(1285*pi/9))*sin(2593*pi/18)*cos(pi/9)=1/8:=
begin
have : sin(2593 * pi / 18) * cos(pi / 9) * (-sin(1285 * pi / 9) * sin(pi) + cos(1285 * pi / 9) * cos(pi)) = (-sin(pi)*sin(1285*pi/9) + cos(pi)*cos(1285*pi/9))*sin(2593*pi/18)*cos(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1294*pi/9) = -sin(1285*pi/9) * sin(pi) + cos(1285*pi/9) * cos(pi),
{
have : cos(1294*pi/9) = cos((1285*pi/9) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = sin(2593*pi/18),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/18) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = cos(1294*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/9) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw mul_assoc,
have : cos(pi/9)*cos(2*pi/9) = cos(pi/3)/2 + cos(-pi/9)/2,
{
rw cos_mul_cos,
have : cos((pi/9) + (2*pi/9)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/9) - (2*pi/9)) = cos(-pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(-pi/9) = cos(pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
have : sin(pi/18) = cos(4*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(4*pi/9)*(1/2/2 + cos(pi/9)/2) = cos(4*pi/9)/4 + cos(pi/9)*cos(4*pi/9)/2,
{
ring_exp,
},
rw this,
have : cos(pi/9)*cos(4*pi/9)/2 = cos(5*pi/9)/4 + cos(pi/3)/4,
{
have : cos(pi/9)*cos(4*pi/9) = cos(pi/3)/2 + cos(5*pi/9)/2,
{
rw mul_comm,
rw cos_mul_cos,
have : cos((4*pi/9) + (pi/9)) = cos(5*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : cos((4*pi/9) - (pi/9)) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
rw cos_pi_div_three,
have : cos(5*pi/9) = -cos(4*pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_214_HHTA_extend(h0 : cos (pi/8) ≠ 0) (h1: 2 + sqrt(2) ≠ 0) (h3 : cos(pi/8)≠ 0) (h4 : (sin(pi/8)/cos(pi/8))≠ 0) (h5 : sin(pi/8)≠ 0) (h6 : cos(pi/16)≠ 0) (h7 : (1-tan(pi/16)**2)≠ 0) : -cos(pi/8)/sin(pi/8) + 2*tan(pi/16)/(1 - tan(pi/16)**2)=-2:=
begin
have : tan(pi/8) = 2 * tan(pi/16) / ( 1 - tan(pi/16) ** 2 ),
{
have : tan(pi/8) = tan(2*(pi/16)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) / cos(pi/8) = tan(pi/8),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/8) / cos(pi/8)) = sin(pi/8)/cos(pi/8),
{
ring,
},
have : sin(pi / 8) / cos(pi / 8) - 1 / (sin(pi / 8) / cos(pi / 8)) = -cos(pi/8)/sin(pi/8) + sin(pi/8)/cos(pi/8),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = sin(pi/8) / cos(pi/8),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(pi/8) = sin(pi/4)/(1+cos(pi/4)),
{
have : cos(pi/8) = cos((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this at *,
have : tan(pi/8) = tan((pi/4)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_215_CBML_extend (h0 : cos(56*pi/45)≠ 0) (h1 : (2*cos(56*pi/45))≠ 0) (h2 : cos(56*pi/45)≠ 0) : sin(2*pi/45)*sin(112*pi/45)*cos(2*pi/45)/cos(56*pi/45) + cos(4*pi/45)*cos(7729*pi/45)=1/2:=
begin
have : 2 * sin(2 * pi / 45) * cos(2 * pi / 45) * sin(112 * pi / 45) / (2 * cos(56 * pi / 45)) + cos(4 * pi / 45) * cos(7729 * pi / 45) = sin(2*pi/45)*sin(112*pi/45)*cos(2*pi/45)/cos(56*pi/45) + cos(4*pi/45)*cos(7729*pi/45),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/45) = 2 * sin(2*pi/45) * cos(2*pi/45),
{
have : sin(4*pi/45) = sin(2*(2*pi/45)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 45) * (sin(112 * pi / 45) / (2 * cos(56 * pi / 45))) + cos(4 * pi / 45) * cos(7729 * pi / 45) = sin(4*pi/45)*sin(112*pi/45)/(2*cos(56*pi/45)) + cos(4*pi/45)*cos(7729*pi/45),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(56*pi/45) = sin(112*pi/45) / ( 2 * cos(56*pi/45) ),
{
have : sin(112*pi/45) = sin(2*(56*pi/45)),
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
have : sin(4 * pi / 45) * sin(56 * pi / 45) + cos(7729 * pi / 45) * cos(4 * pi / 45) = sin(4*pi/45)*sin(56*pi/45) + cos(4*pi/45)*cos(7729*pi/45),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/90) = cos(7729*pi/45),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (23*pi/90) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(56*pi/45) = -sin(11*pi/45),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (56*pi/45) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(23*pi/90) = cos(11*pi/45),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (23*pi/90) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_neg,
rw ← neg_mul,
rw mul_comm (cos(11*pi/45)) (cos(4*pi/45)),
have : -sin(4*pi/45)*sin(11*pi/45) + cos(4*pi/45)*cos(11*pi/45) = cos(pi/3),
{
have : cos(pi/3) = cos((4*pi/45) + (11*pi/45)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_three,
end


lemma Trigo_2_216_YACW_extend(h0: sin(pi/9) ≠ 0) (h1 : (-sin(7*pi/36)**2+cos(29*pi/36)**2)≠ 0) (h2 : (-sin(7*pi/36)**2+(-sin(29*pi/72)**2+cos(29*pi/72)**2)**2)≠ 0) (h3 : (-sin(7*pi/36)**2+(-cos(10375*pi/72)**2+cos(29*pi/72)**2)**2)≠ 0) : sin(-13*pi/9)*cos(184*pi/9)/(-sin(7*pi/36)**2 + (-cos(10375*pi/72)**2 + cos(29*pi/72)**2)**2)=1/2:=
begin
have : sin((-13) * pi / 9) * cos(184 * pi / 9) / (-sin(7 * pi / 36) ** 2 + (-cos(10375 * pi / 72) ** 2 + cos(29 * pi / 72) ** 2) ** 2) = sin(-13*pi/9)*cos(184*pi/9)/(-sin(7*pi/36)**2 + (-cos(10375*pi/72)**2 + cos(29*pi/72)**2)**2),
{
field_simp at *,
},
have : sin(29*pi/72) = cos(10375*pi/72),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (29*pi/72) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-13) * pi / 9) * cos(184 * pi / 9) / (-sin(7 * pi / 36) ** 2 + (-sin(29 * pi / 72) ** 2 + cos(29 * pi / 72) ** 2) ** 2) = sin(-13*pi/9)*cos(184*pi/9)/(-sin(7*pi/36)**2 + (-sin(29*pi/72)**2 + cos(29*pi/72)**2)**2),
{
field_simp at *,
},
have : cos(29*pi/36) = -sin(29*pi/72) ** 2 + cos(29*pi/72) ** 2,
{
have : cos(29*pi/36) = cos(2*(29*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin((-13) * pi / 9) * cos(184 * pi / 9) / (-sin(7 * pi / 36) ** 2 + cos(29 * pi / 36) ** 2) = sin(-13*pi/9)*cos(184*pi/9)/(-sin(7*pi/36)**2 + cos(29*pi/36)**2),
{
field_simp at *,
},
have : cos(4*pi/9) = cos(184*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (4*pi/9) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(29*pi/36) = -cos(7*pi/36),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (29*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw neg_sq,
have : -sin(7*pi/36)**2 + cos(7*pi/36)**2 = cos(7*pi/18),
{
have : cos(7*pi/18) = cos(2*(7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : cos(7*pi/18) = sin(pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-13*pi/9) = sin(4*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-13*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_218_JEUS_extend(h0 : cos(pi/12) ≠ 0) (h1 : -sin(π/12)**2 + cos(π/12)**2 ≠ 0) (h2 : cos((pi/6)/2)≠ 0) (h3 : ((-(1-cos(pi/6))**2/sin(pi/6)**2+1)*sin(pi/6))≠ 0) (h4 : sin(pi/6)≠ 0) (h5 : (1-((1-cos(pi/6))/sin(pi/6))**2)≠ 0) (h6 : ((-(1-cos(pi/6))**2/sin(427*pi/6)**2+1)*sin(427*pi/6))≠ 0) (h7 : sin(427*pi/6)≠ 0) (h8 : ((-(1-cos(pi/6))**2/(-sin(427*pi/6))**2+1)*-sin(427*pi/6))≠ 0) (h9 : (-sin(427*pi/6))≠ 0) (h10 : sin(991*pi/6)≠ 0) (h11 : ((-(1-cos(pi/6))**2/sin(991*pi/6)**2+1)*sin(991*pi/6))≠ 0) : (-1 + cos(pi/6))/((-(1 - cos(pi/6))**2/sin(991*pi/6)**2 + 1)*sin(991*pi/6))=sqrt(3)/6:=
begin
have : -(1 - cos(pi / 6)) / ((-(1 - cos(pi / 6)) ** 2 / sin(991 * pi / 6) ** 2 + 1) * sin(991 * pi / 6)) = (-1 + cos(pi/6))/((-(1 - cos(pi/6))**2/sin(991*pi/6)**2 + 1)*sin(991*pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(427*pi/6) = sin(991*pi/6),
{
rw sin_eq_sin_add_int_mul_two_pi (427*pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos(pi / 6)) / ((-(1 - cos(pi / 6)) ** 2 / (-sin(427 * pi / 6)) ** 2 + 1) * -sin(427 * pi / 6)) = -(1 - cos(pi/6))/((-(1 - cos(pi/6))**2/sin(427*pi/6)**2 + 1)*sin(427*pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = -sin(427*pi/6),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/6) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos(pi / 6)) / sin(pi / 6) / (1 - ((1 - cos(pi / 6)) / sin(pi / 6)) ** 2) = (1 - cos(pi/6))/((-(1 - cos(pi/6))**2/sin(pi/6)**2 + 1)*sin(pi/6)),
{
field_simp at *,
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
rw tan_eq_sin_div_cos,
rw div_pow,
have : 1 - sin(pi/12)**2/cos(pi/12)**2 = (-sin(pi/12)**2 + cos(pi/12)**2)/cos(pi/12)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sin(pi/12)/cos(pi/12)/((-sin(pi/12)**2 + cos(pi/12)**2)/cos(pi/12)**2) = sin(pi/12)*cos(pi/12)/(-sin(pi/12)**2 + cos(pi/12)**2),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
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
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
have : sqrt 3 ≠ 0,
{
rw sqrt_ne_zero,
linarith,
repeat {linarith},
},
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_219_KWSA_extend(h0 : cos(3*pi/20) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : 1 - tan(pi/10) * tan(3*pi/20) ≠ 0)  (h3 : cos(3*pi/20)≠ 0) (h4 : cos(pi/10)≠ 0) (h5 : 1 - tan(3*pi/20) * tan(pi/10)≠ 0) : -tan(pi/10)*tan(1977*pi/20) + (tan(pi/10)*tan(1977*pi/20) + 1)*tan(65*pi/4)=1:=
begin
have : tan(pi/4) = tan(65*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (pi/4) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi / 10) * -tan(1977 * pi / 20) + (-tan(pi / 10) * -tan(1977 * pi / 20) + 1) * tan(pi / 4) = -tan(pi/10)*tan(1977*pi/20) + (tan(pi/10)*tan(1977*pi/20) + 1)*tan(pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/20) = -tan(1977*pi/20),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/20) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-tan(3 * pi / 20) * tan(pi / 10) + 1) * tan(pi / 4) + tan(pi / 10) * tan(3 * pi / 20) = tan(pi/10)*tan(3*pi/20) + (-tan(pi/10)*tan(3*pi/20) + 1)*tan(pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/20) + tan(pi/10) = ( -tan(3*pi/20) * tan(pi/10) + 1 ) * tan(pi/4),
{
rw tan_add_tan,
have : tan((3*pi/20) + (pi/10)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(3*pi/20) + tan(pi/10)) + tan(pi/10)*tan(3*pi/20) = tan(pi/10)*tan(3*pi/20)+tan(pi/10)+tan(3*pi/20),
{
ring,
},
conv {to_lhs, rw this,},
rw add_assoc,
have : tan(pi/10) + tan(3*pi/20) = (-tan(pi/10)*tan(3*pi/20) + 1)*tan(pi/4),
{
rw tan_add_tan,
have : tan((pi/10) + (3*pi/20)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/10)*tan(3*pi/20) + 1)*tan(pi/4) = -tan(pi/10)*tan(3*pi/20)*tan(pi/4) + tan(pi/4),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_four, -cos_pi_div_four, -sin_pi_div_two, -cos_pi_div_two],
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_2_220_ZJNX_extend : -sin(29*pi/180)*sin(91*pi/180) - sin(1165*pi/6)/2 + sin(13507*pi/45)/2=-1/2:=
begin
have : -sin(29 * pi / 180) * sin(91 * pi / 180) - sin(1165 * pi / 6) / 2 - -sin(13507 * pi / 45) / 2 = -sin(29*pi/180)*sin(91*pi/180) - sin(1165*pi/6)/2 + sin(13507*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-8647*pi/45) = -sin(13507*pi/45),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-8647*pi/45) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(29 * pi / 180) * sin(91 * pi / 180) - (sin((-8647) * pi / 45) / 2 + sin(1165 * pi / 6) / 2) = -sin(29*pi/180)*sin(91*pi/180) - sin(1165*pi/6)/2 - sin(-8647*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(181*pi/180) * cos(34769*pi/180) = sin(-8647*pi/45) / 2 + sin(1165*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((181*pi/180) + (34769*pi/180)) = sin(1165*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((181*pi/180) - (34769*pi/180)) = sin(-8647*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(181*pi/180) * cos(34769*pi/180)) = sin(181*pi/180)*cos(34769*pi/180),
{
ring,
},
have : -sin(29 * pi / 180) * sin(91 * pi / 180) + -cos(34769 * pi / 180) * sin(181 * pi / 180) = -sin(29*pi/180)*sin(91*pi/180) - sin(181*pi/180)*cos(34769*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(119*pi/180) = -cos(34769*pi/180),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (119*pi/180) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(119*pi/180) = cos(29*pi/180),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (119*pi/180) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(181*pi/180) = -sin(pi/180),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (181*pi/180) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(91*pi/180) = cos(pi/180),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (91*pi/180) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_neg,
rw ← sub_eq_add_neg,
rw mul_comm (cos(29*pi/180)) (sin(pi/180)),
have : -sin(29*pi/180)*cos(pi/180) - sin(pi/180)*cos(29*pi/180) = -sin(pi/6),
{
have : sin(pi/6) = sin(pi/180)*cos(29*pi/180) + sin(29*pi/180)*cos(pi/180),
{
have : sin(pi/6) = sin((pi/180) + (29*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_2_221_IETY_extend(h0 : cos(2) ≠ 0)  (h1 : cos(1 - 2*pi)≠ 0) (h2 : (1-tan(1-2*pi)**2)≠ 0) (h3 : cos(1-2*pi)≠ 0) (h4 : ((-sin(1-2*pi)**2/cos(1-2*pi)**2+1)*cos(1-2*pi))≠ 0) (h5 : (1-(sin(1-2*pi)/cos(1-2*pi))**2)≠ 0) (h6 : ((-(1-cos(1-2*pi)**2)/cos(1-2*pi)**2+1)*cos(1-2*pi))≠ 0) : 2*sin(1 - 2*pi)*cos(2 - pi)/((-(1 - cos(1 - 2*pi)**2)/cos(1 - 2*pi)**2 + 1)*cos(1 - 2*pi)) + sin(-2)=-2*sin(2):=
begin
have : sin(1 - 2*pi) ** 2 = 1 - cos(1 - 2*pi) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 2 * cos(2 - pi) * (sin(1 - 2 * pi) / cos(1 - 2 * pi)) / (1 - (sin(1 - 2 * pi) / cos(1 - 2 * pi)) ** 2) + sin(-2) = 2*sin(1 - 2*pi)*cos(2 - pi)/((-sin(1 - 2*pi)**2/cos(1 - 2*pi)**2 + 1)*cos(1 - 2*pi)) + sin(-2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(1 - 2*pi) = sin(1 - 2*pi) / cos(1 - 2*pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sin(-2) + cos(2 - pi) * (2 * tan(1 - 2 * pi) / (1 - tan(1 - 2 * pi) ** 2)) = 2*cos(2 - pi)*tan(1 - 2*pi)/(1 - tan(1 - 2*pi)**2) + sin(-2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2 - 4*pi) = 2 * tan(1 - 2*pi) / ( 1 - tan(1 - 2*pi) ** 2 ),
{
have : tan(2 - 4*pi) = tan(2*(1 - 2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : cos(2 - pi) = -cos(2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2 - pi) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(2 - 4*pi) = tan(2),
{
rw tan_eq_tan_add_int_mul_pi (2 - 4*pi) (4),
repeat {apply congr_arg _},
simp,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring_exp,
end


lemma Trigo_2_222_ZDRD_extend : sin(pi/45)/2 - sin(-997*pi/45)*sin(61*pi/90) + sin(2*pi/3)/2=sqrt(3)/2:=
begin
have : sin(pi / 45) / 2 - sin(61 * pi / 90) * sin((-997) * pi / 45) + sin(2 * pi / 3) / 2 = sin(pi/45)/2 - sin(-997*pi/45)*sin(61*pi/90) + sin(2*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4102*pi/45) = sin(-997*pi/45),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4102*pi/45) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 45) / 2 + sin(61 * pi / 90) * -sin(4102 * pi / 45) + sin(2 * pi / 3) / 2 = sin(pi/45)/2 - sin(61*pi/90)*sin(4102*pi/45) + sin(2*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(31*pi/90) = -sin(4102*pi/45),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (31*pi/90) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 45) / 2 + sin(2 * pi / 3) / 2 + sin(61 * pi / 90) * cos(31 * pi / 90) = sin(pi/45)/2 + sin(61*pi/90)*cos(31*pi/90) + sin(2*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(31*pi/90) * cos(29*pi/90) = sin(pi/45) / 2 + sin(2*pi/3) / 2,
{
rw sin_mul_cos,
have : sin((31*pi/90) + (29*pi/90)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((31*pi/90) - (29*pi/90)) = sin(pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(31*pi/90) * cos(29*pi/90)) = sin(31*pi/90)*cos(29*pi/90),
{
ring,
},
have : sin(61*pi/90)*cos(31*pi/90) = sin(46*pi/45)/2 + sin(pi/3)/2,
{
rw sin_mul_cos,
have : sin((61*pi/90) + (31*pi/90)) = sin(46*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin((61*pi/90) - (31*pi/90)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(46*pi/45) = -sin(pi/45),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (46*pi/45) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -sin(pi/45)/2 + sin(pi/3)/2 = sin(7*pi/45)*cos(8*pi/45),
{
have : -sin(pi/45) + sin(pi/3) = 2*sin(7*pi/45)*cos(8*pi/45),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((pi/3) + (pi/45))/2) = cos(8*pi/45),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/3) - (pi/45))/2) = sin(7*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : sin(7*pi/45) = cos(31*pi/90),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/45) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(8*pi/45) = sin(29*pi/90),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (8*pi/45) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_comm (cos(31*pi/90)) (sin(29*pi/90)),
have : sin(29*pi/90)*cos(31*pi/90) + sin(31*pi/90)*cos(29*pi/90) = sin(2*pi/3),
{
have : sin(2*pi/3) = sin((29*pi/90) + (31*pi/90)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_2_223_RDSG_extend(h0 : cos(x) ≠ 0)  (h1 : sin(x+5*pi/2)≠ 0) (h2 : -cos(-x+77*pi)≠ 0) (h3 : cos(-x+77*pi)≠ 0) : -(cos(2*x - 5*pi/2)/2 + cos(3*pi/2)/2)*cos(-x + 385*pi/2)/cos(-x + 77*pi)=sin(x)**2:=
begin
have : cos(x - pi/2) * cos(-x + 2*pi) = cos(2*x - 5*pi/2) / 2 + cos(3*pi/2) / 2,
{
rw cos_mul_cos,
have : cos((x - pi/2) + (-x + 2*pi)) = cos(3*pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((x - pi/2) - (-x + 2*pi)) = cos(2*x - 5*pi/2),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(cos(x - pi/2) * cos(-x + 2*pi))*cos(-x + 385*pi/2)/cos(-x + 77*pi) = -cos(-x+2*pi)*cos(-x+385*pi/2)*cos(x-pi/2)/cos(-x+77*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(-x + 2 * pi) * cos(-x + 385 * pi / 2) * cos(x - pi / 2) / -cos(-x + 77 * pi) = -cos(-x + 2*pi)*cos(-x + 385*pi/2)*cos(x - pi/2)/cos(-x + 77*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x + 5*pi/2) = -cos(-x + 77*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 5*pi/2) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 385 * pi / 2) * cos(-x + 2 * pi) * cos(x - pi / 2) / sin(x + 5 * pi / 2) = cos(-x + 2*pi)*cos(-x + 385*pi/2)*cos(x - pi/2)/sin(x + 5*pi/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - 2*pi) = cos(-x + 385*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (x - 2*pi) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - 2*pi) = sin(x),
{
rw sin_eq_sin_add_int_mul_two_pi (x - 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x - pi/2) = sin(x),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x - pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(x + 5*pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 5*pi/2) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_224_VDAS_extend : -sin(pi/3)**2 + sqrt(3)*(-cos(-pi/6)*cos(140*pi/3) - sin(-pi/6)*sin(427*pi/3))/2=0:=
begin
have : -sin(pi / 3) ** 2 + sqrt 3 * (-cos(140 * pi / 3) * cos(-pi / 6) - sin(-pi / 6) * sin(427 * pi / 3)) / 2 = -sin(pi/3)**2 + sqrt(3)*(-cos(-pi/6)*cos(140*pi/3) - sin(-pi/6)*sin(427*pi/3))/2,
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/6) = -cos(140*pi/3),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 3) ** 2 + sqrt 3 * (sin(5 * pi / 6) * cos(-pi / 6) + sin(-pi / 6) * -sin(427 * pi / 3)) / 2 = -sin(pi/3)**2 + sqrt(3)*(sin(5*pi/6)*cos(-pi/6) - sin(-pi/6)*sin(427*pi/3))/2,
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/6) = -sin(427*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/6) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 3) ** 2 + sqrt 3 * (sin(5 * pi / 6) * cos(-pi / 6) + sin(-pi / 6) * cos(5 * pi / 6)) / 2 = -sin(pi/3)**2 + sqrt(3)*(sin(5*pi/6)*cos(-pi/6) + sin(-pi/6)*cos(5*pi/6))/2,
{
field_simp at *,
},
have : sin(2*pi/3) = sin(5*pi/6) * cos(-pi/6) + sin(-pi/6) * cos(5*pi/6),
{
have : sin(2*pi/3) = sin((5*pi/6) + (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_pi_div_three,
rw sin_two_pi_div_three,
norm_num,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_225_YWGR_extend(h0 : cos(pi/18) ≠ 0)  (h1 : (sin(2*pi/9)*cos(2*pi/9))≠ 0) (h2 : (sin(2*pi/9)*cos(200*pi/9))≠ 0) (h3 : (sin(2*pi/9)*sin(2885*pi/18))≠ 0) : (-sin(pi/36)**2 + sin(4159*pi/36)**2)/(sin(2*pi/9)*sin(2885*pi/18))=2:=
begin
have : cos(200*pi/9) = sin(2885*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (200*pi/9) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = cos(200*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (2*pi/9) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi / 36) ** 2 + (-sin(4159 * pi / 36)) ** 2) / (sin(2 * pi / 9) * cos(2 * pi / 9)) = (-sin(pi/36)**2 + sin(4159*pi/36)**2)/(sin(2*pi/9)*cos(2*pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/36) = -sin(4159*pi/36),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/36) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/36)**2 + cos(pi/36)**2 = cos(pi/18),
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
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/9) = cos(pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_226_DVUW_extend (h0 : cos(143*pi/12)≠ 0) (h1 : (2*cos(143*pi/12))≠ 0) : (-sin(143*pi/6)/(2*cos(143*pi/12)) + cos(697*pi/12))*(-cos(697*pi/12) - sin(143*pi/6)/(2*cos(143*pi/12)))=-sqrt(3)/2:=
begin
have : (-(sin(143 * pi / 6) / (2 * cos(143 * pi / 12))) + cos(697 * pi / 12)) * (-cos(697 * pi / 12) - sin(143 * pi / 6) / (2 * cos(143 * pi / 12))) = (-sin(143*pi/6)/(2*cos(143*pi/12)) + cos(697*pi/12))*(-cos(697*pi/12) - sin(143*pi/6)/(2*cos(143*pi/12))),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(143*pi/12) = sin(143*pi/6) / ( 2 * cos(143*pi/12) ),
{
have : sin(143*pi/6) = sin(2*(143*pi/12)),
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
have : (-sin(143 * pi / 12) + cos(697 * pi / 12)) * (-cos(697 * pi / 12) + -sin(143 * pi / 12)) = (-sin(143*pi/12) + cos(697*pi/12))*(-cos(697*pi/12) - sin(143*pi/12)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(143*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (6),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 12) - cos(697 * pi / 12)) * (sin(pi / 12) + cos(697 * pi / 12)) = (sin(pi/12) + cos(697*pi/12))*(-cos(697*pi/12) + sin(pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = cos(697*pi/12),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/12) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/12) - cos(pi/12))*(sin(pi/12) + cos(pi/12)) = -cos(pi/12)**2 + sin(pi/12)**2,
{
ring_exp,
},
rw this,
have : -cos(pi/12)**2 + sin(pi/12)**2 = -cos(pi/6),
{
have : cos(pi/6) = -sin(pi/12)**2 + cos(pi/12)**2,
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
linarith,
},
rw this,
have : -cos(pi/6) = -sqrt(3)/2,
{
have : cos(pi/6) = sqrt(3)/2,
{
rw cos_pi_div_six,
},
linarith,
},
rw this,
end


lemma Trigo_2_227_EXKN_extend : sin(112*pi/3)*cos(535*pi/6)*tan(21*pi/4)=3/4:=
begin
have : cos(535 * pi / 6) * sin(112 * pi / 3) * tan(21 * pi / 4) = sin(112*pi/3)*cos(535*pi/6)*tan(21*pi/4),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(967*pi/6) = sin(112*pi/3),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (967*pi/6) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/3) = cos(535*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/3) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(19*pi/6) = cos(967*pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (19*pi/6) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
have : cos(19*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (19*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
have : tan(21*pi/4) = tan(pi/4),
{
rw tan_eq_tan_add_int_mul_pi (21*pi/4) (-5),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_four,
norm_num,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_228_OWVU_extend(h0: cos(2) ≤ 0) : sqrt(4 - 4*(sin(2 - pi/2)*cos(pi/2) + sin(pi/2)*cos(2 - pi/2))**2)=-2 + 4*sin(1)**2:=
begin
have : sin(2) = sin(2 - pi/2) * cos(pi/2) + sin(pi/2) * cos(2 - pi/2),
{
have : sin(2) = sin((2 - pi/2) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * (1 - 2 * sin(1) ** 2) = -2 + 4*sin(1)**2,
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2) = 1 - 2 * sin(1) ** 2,
{
have : cos(2) = cos(2*(1)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_rhs, rw ← this,},
have : sqrt (2 * (1 - 2 * sin(2) ** 2) + 2) = sqrt(4 - 4*sin(2)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4) = 1 - 2 * sin(2) ** 2,
{
have : cos(4) = cos(2*(2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(4) = -1 + 2*cos(2)**2,
{
have : cos(4) = cos(2*(2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
ring_exp,
rw sqrt_mul',
have : sqrt(4)= sqrt(2**2),
{
apply congr_arg,
ring,
},
rw this,
repeat {rw sqrt_sq_eq_abs},
rw abs_eq_neg_self.mpr h0,
rw abs_eq_self.mpr,
ring,
repeat {linarith},
end


lemma Trigo_2_229_KMZX_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (2*sin(x)*cos(x))≠ 0) (h3 : (sin(x)*cos(x))≠ 0) (h4 : cos(x - pi/3)≠ 0) (h5 : cos(-pi/3)≠ 0) (h6 : ((tan(x-pi/3)-tan(-pi/3))/(1+tan(x-pi/3)*tan(-pi/3)))≠ 0) (h7 : (tan(x-pi/3)-tan(-pi/3))≠ 0) (h8 : (tan(-pi/3)*tan(x-pi/3)+1)≠ 0) (h9 : (1+tan(x-pi/3)*tan(-pi/3))≠ 0) (h10 : (sin(x+70*pi)*cos(x))≠ 0) : (tan(-pi/3)*tan(x - pi/3) + 1)/(tan(x - pi/3) - tan(-pi/3)) + (tan(x - pi/3) - tan(-pi/3))/(tan(-pi/3)*tan(x - pi/3) + 1)=1/(sin(x + 70*pi)*cos(x)):=
begin
have : sin(x) = sin(x + 70*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (x) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (tan(x - pi / 3) - tan(-pi / 3)) / (1 + tan(x - pi / 3) * tan(-pi / 3)) + 1 / ((tan(x - pi / 3) - tan(-pi / 3)) / (1 + tan(x - pi / 3) * tan(-pi / 3))) = (tan(-pi/3)*tan(x - pi/3) + 1)/(tan(x - pi/3) - tan(-pi/3)) + (tan(x - pi/3) - tan(-pi/3))/(tan(-pi/3)*tan(x - pi/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x) = ( tan(x - pi/3) - tan(-pi/3) ) / ( 1 + tan(x - pi/3) * tan(-pi/3) ),
{
have : tan(x) = tan((x - pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : 2 / (2 * sin(x) * cos(x)) = 1/(sin(x)*cos(x)),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2*x) = 2 * sin(x) * cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
conv {to_rhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
rw one_div_div,
have : sin(x)/cos(x) + cos(x)/sin(x) = (sin(x)**2 + cos(x)**2)/(sin(x)*cos(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
field_simp,
ring_exp,
end


lemma Trigo_2_230_NIZW_extend (h0 : cos(x)≠ 0) (h1 : (2*cos(x))≠ 0) (h2 : (2*cos(x)**2)≠ 0) (h3 : (2*(-sin(x/2)**2+cos(x/2)**2)**2)≠ 0) (h4 : (2*(-sin(x/2)**2+sin(-x/2+15*pi/2)**2)**2)≠ 0) (h5 : (2*(-sin(x/2)**2+(-sin(-x/2+15*pi/2))**2)**2)≠ 0) : cos(2*x) + 1 + sin(2*x)**2/(2*(-sin(x/2)**2 + sin(-x/2 + 15*pi/2)**2)**2)=2:=
begin
have : cos(2 * x) + 1 + sin(2 * x) ** 2 / (2 * (-sin(x / 2) ** 2 + (-sin(-x / 2 + 15 * pi / 2)) ** 2) ** 2) = cos(2*x) + 1 + sin(2*x)**2/(2*(-sin(x/2)**2 + sin(-x/2 + 15*pi/2)**2)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x/2) = -sin(-x/2 + 15*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x/2) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * x) ** 2 / (2 * (-sin(x / 2) ** 2 + cos(x / 2) ** 2) ** 2) + cos(2 * x) + 1 = cos(2*x) + 1 + sin(2*x)**2/(2*(-sin(x/2)**2 + cos(x/2)**2)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -sin(x/2) ** 2 + cos(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sin(2 * x) / (2 * cos(x))) ** 2 + cos(2 * x) + 1 = sin(2*x)**2/(2*cos(x)**2) + cos(2*x) + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = sin(2*x) / ( 2 * cos(x) ),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
ring,
rw ← add_assoc,
rw sin_sq_add_cos_sq,
norm_num,
end


lemma Trigo_2_231_MJDQ_extend (h0 : cos(7*pi/36)≠ 0) (h1 : (2*cos(7*pi/36))≠ 0) : cos(7*pi/36)*cos(4*pi/9) + sin(-1183*pi/9)*sin(7*pi/18)/(2*cos(7*pi/36))=sqrt(2)/2:=
begin
have : cos(7 * pi / 36) * cos(4 * pi / 9) + sin(7 * pi / 18) * sin((-1183) * pi / 9) / (2 * cos(7 * pi / 36)) = cos(7*pi/36)*cos(4*pi/9) + sin(-1183*pi/9)*sin(7*pi/18)/(2*cos(7*pi/36)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1786*pi/9) = sin(-1183*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (1786*pi/9) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = sin(1786*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (4*pi/9) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 18) / (2 * cos(7 * pi / 36)) * sin(4 * pi / 9) + cos(7 * pi / 36) * cos(4 * pi / 9) = cos(7*pi/36)*cos(4*pi/9) + sin(7*pi/18)*sin(4*pi/9)/(2*cos(7*pi/36)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/36) = sin(7*pi/18) / ( 2 * cos(7*pi/36) ),
{
have : sin(7*pi/18) = sin(2*(7*pi/36)),
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
rw add_comm,
have : cos(7*pi/36)*cos(4*pi/9) + sin(7*pi/36)*sin(4*pi/9) = cos(-pi/4),
{
have : cos(-pi/4) = cos((7*pi/36) - (4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
},
rw this,
have : cos(-pi/4) = cos(pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_2_232_WIUI_extend (h0 : sin(5*x)≠ 0) (h1 : (2*sin(5*x))≠ 0) : sin(-pi/3)*sin(5*x - pi/3) + cos(3*x) + cos(-pi/3)*cos(5*x - pi/3)=2*cos(4*x)*cos(x):=
begin
have : cos(3 * x) + (sin(5 * x - pi / 3) * sin(-pi / 3) + cos(5 * x - pi / 3) * cos(-pi / 3)) = sin(-pi/3)*sin(5*x - pi/3) + cos(3*x) + cos(-pi/3)*cos(5*x - pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*x) = sin(5*x - pi/3) * sin(-pi/3) + cos(5*x - pi/3) * cos(-pi/3),
{
have : cos(5*x) = cos((5*x - pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3 * x) + 2 * sin(5 * x) * cos(5 * x) / (2 * sin(5 * x)) = cos(3*x) + cos(5*x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(10*x) = 2 * sin(5*x) * cos(5*x),
{
have : sin(10*x) = sin(2*(5*x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(5*x) = sin(10*x) / ( 2 * sin(5*x) ),
{
have : sin(10*x) = sin(2*(5*x)),
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
rw mul_assoc,
have : cos(4*x)*cos(x) = cos(3*x)/2 + cos(5*x)/2,
{
rw cos_mul_cos,
have : cos((4*x) + (x)) = cos(5*x),
{
apply congr_arg,
ring,
},
rw this,
have : cos((4*x) - (x)) = cos(3*x),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
ring_exp,
end


lemma Trigo_2_234_GIRS_extend(h0 : cos((x*4 + π)/4) ≠ 0) (h1 : sin((x*4 + π)/4) ≠ 0) (h2 : cos(2*x) ≠ 0)  (h3 : (cos(x+pi/4)**2*tan(x+169*pi/4))≠ 0) (h4 : (cos(-x+775*pi/4)**2*tan(x+169*pi/4))≠ 0) (h5 : ((1-2*sin(-x/2+775*pi/8)**2)**2*tan(x+169*pi/4))≠ 0) : (4*cos(x)**4 - 2*cos(2*x) - 1)/((1 - 2*sin(-x/2 + 775*pi/8)**2)**2*tan(x + 169*pi/4))=2*cos(2*x):=
begin
have : cos(-x + 775*pi/4) = 1 - 2 * sin(-x/2 + 775*pi/8) ** 2,
{
have : cos(-x + 775*pi/4) = cos(2*(-x/2 + 775*pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(x + pi/4) = cos(-x + 775*pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x + pi/4) (97),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi/4) = tan(x + 169*pi/4),
{
rw tan_eq_tan_add_int_mul_pi (x + pi/4) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_right_comm,
have : 4*cos(x)**4 - 1 = (2*cos(x)**2 - 1)*(2*cos(x)**2 + 1),
{
ring_exp,
},
rw this,
have : 2*cos(x)**2 - 1 = cos(2*x),
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
rw this,
have : cos(2*x)*(2*cos(x)**2 + 1) - 2*cos(2*x) = (2*cos(x)**2 - 1)*cos(2*x),
{
ring_exp,
},
rw this,
have : 2*cos(x)**2 - 1 = cos(2*x),
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
rw this,
rw tan_eq_sin_div_cos,
have : cos(2*x)*cos(2*x)/(cos(x + pi/4)**2*(sin(x + pi/4)/cos(x + pi/4))) = cos(2*x)*cos(2*x)/(cos(x + pi/4)*sin(x + pi/4)),
{
field_simp,
ring,
},
rw this,
rw mul_comm (cos(x + pi/4)) (sin(x + pi/4)),
have : sin(x + pi/4)*cos(x + pi/4) = sin(2*x + pi/2)/2,
{
have : sin(2*x + pi/2) = 2*sin(x + pi/4)*cos(x + pi/4),
{
have : sin(2*x + pi/2) = sin(2*(x + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*x + pi/2) = cos(2*x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_235_PZHG_extend : sin(pi/18)*cos(1277*pi/9) + sin(8*pi/9)*cos(3599*pi/18)=1/2:=
begin
have : sin(pi / 18) * cos(1277 * pi / 9) - sin(8 * pi / 9) * -cos(3599 * pi / 18) = sin(pi/18)*cos(1277*pi/9) + sin(8*pi/9)*cos(3599*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1201*pi/9) = -cos(3599*pi/18),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1201*pi/9) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 18) * cos(1277 * pi / 9) + -sin(1201 * pi / 9) * sin(8 * pi / 9) = sin(pi/18)*cos(1277*pi/9) - sin(8*pi/9)*sin(1201*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = -sin(1201*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/9) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = cos(1277*pi/9),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/9) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = cos(pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_comm (cos(pi/18)) (sin(pi/9)),
have : sin(pi/18)*cos(pi/9) + sin(pi/9)*cos(pi/18) = sin(pi/6),
{
have : sin(pi/6) = sin((pi/9) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_2_236_IXFH_extend(h0 : 3 - cos(π/9) ≠ 0)  (h1 : (2-((-4)*sin(4*pi/27)**3+3*sin(4*pi/27))**2)≠ 0) (h2 : (2-(-4*sin(4*pi/27)**3+3*sin(4*pi/27))**2)≠ 0) (h3 : (2-((-4)*(-sin(4837*pi/27))**3+3*-sin(4837*pi/27))**2)≠ 0) (h4 : (2-(4*sin(4837*pi/27)**3-3*sin(4837*pi/27))**2)≠ 0) : (3 - sin(1087*pi/18))/(2 - (4*sin(4837*pi/27)**3 - 3*sin(4837*pi/27))**2)=2:=
begin
have : (3 - sin(1087 * pi / 18)) / (2 - ((-4) * (-sin(4837 * pi / 27)) ** 3 + 3 * -sin(4837 * pi / 27)) ** 2) = (3 - sin(1087*pi/18))/(2 - (4*sin(4837*pi/27)**3 - 3*sin(4837*pi/27))**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/27) = -sin(4837*pi/27),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/27) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (3 - sin(1087 * pi / 18)) / (2 - ((-4) * sin(4 * pi / 27) ** 3 + 3 * sin(4 * pi / 27)) ** 2) = (3 - sin(1087*pi/18))/(2 - (-4*sin(4*pi/27)**3 + 3*sin(4*pi/27))**2),
{
field_simp at *,
},
have : cos(pi/9) = sin(1087*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (3 - cos(pi / 9)) / (2 - ((-4) * sin(4 * pi / 27) ** 3 + 3 * sin(4 * pi / 27)) ** 2) = (3 - cos(pi/9))/(2 - (-4*sin(4*pi/27)**3 + 3*sin(4*pi/27))**2),
{
field_simp at *,
},
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
have : sin(4*pi/9)**2 = 1/2 - cos(8*pi/9)/2,
{
have : cos(8*pi/9) = cos(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(8*pi/9) = -cos(pi/9),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 2 - (1/2 - -cos(pi/9)/2) = (3 - cos(pi/9))/2,
{
ring,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_237_BRIA_extend(h0 : 2 ≠ 0)  : cos(2*x) - cos(pi/2)=4*sin(2*x/3 + 101*pi/2)**3 - 3*sin(2*x/3 + 101*pi/2):=
begin
have : 2 * (cos(2 * x) / 2 - cos(pi / 2) / 2) = cos(2*x) - cos(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/4) * sin(-x + pi/4) = cos(2*x) / 2 - cos(pi/2) / 2,
{
rw sin_mul_sin,
have : cos((x + pi/4) + (-x + pi/4)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((x + pi/4) - (-x + pi/4)) = cos(2*x),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 2*(sin(x + pi/4) * sin(-x + pi/4)) = 2*sin(-x+pi/4)*sin(x+pi/4),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(2*x/3) = sin(2*x/3 + 101*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*x/3) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(2*x) = 4 * cos(2*x/3) ** 3 - 3 * cos(2*x/3),
{
have : cos(2*x) = cos(3*(2*x/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_rhs, rw ← this,},
have : sin(-x + pi/4) = -sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(-x+pi/4) = sin((pi/4) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(x + pi/4) = sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(x+pi/4) = sin((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
have : -sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x) = sqrt(2)*(-sin(x) + cos(x))/2,
{
ring_exp,
},
rw this,
have : sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x) = sqrt(2)*(sin(x) + cos(x))/2,
{
ring_exp,
},
rw this,
have : cos(2*x) = -sin(x)**2 + cos(x)**2 ,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_238_XBJI_extend(h0 : 1 - sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (1-2*sin(x/2)**2)≠ 0) (h3 : (1-sin(x))≠ 0) (h4 : (1-2*(1-cos(x/2)**2))≠ 0) (h5 : (2*cos(x/2)**2-1)≠ 0) (h6 : (sin(x+9*pi)+1)≠ 0) (h7 : (1- -sin(x+9*pi))≠ 0) : (sin(x + 9*pi) - 1)/(2*cos(x/2)**2 - 1) + (2*cos(x/2)**2 - 1)/(sin(x + 9*pi) + 1)=0:=
begin
have : -(-sin(x + 9 * pi) + 1) / (2 * cos(x / 2) ** 2 - 1) + (2 * cos(x / 2) ** 2 - 1) / (1 - -sin(x + 9 * pi)) = (sin(x + 9*pi) - 1)/(2*cos(x/2)**2 - 1) + (2*cos(x/2)**2 - 1)/(sin(x + 9*pi) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -sin(x + 9*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - 2 * (1 - cos(x / 2) ** 2)) / (1 - sin(x)) - (sin(x) + 1) / (1 - 2 * (1 - cos(x / 2) ** 2)) = -(sin(x) + 1)/(2*cos(x/2)**2 - 1) + (2*cos(x/2)**2 - 1)/(1 - sin(x)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/2) ** 2 = 1 - cos(x/2) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : (1 - 2 * sin(x / 2) ** 2) / (1 - sin(x)) - (1 + sin(x)) / (1 - 2 * sin(x / 2) ** 2) = (1 - 2*sin(x/2)**2)/(1 - sin(x)) - (sin(x) + 1)/(1 - 2*sin(x/2)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = 1 - 2 * sin(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(x)/(1 - sin(x)) - (1 + sin(x))/cos(x) = (cos(x)**2 - (sin(x) + 1)*(1 - sin(x)))/((1 - sin(x))*cos(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : (sin(x) + 1)*(1 - sin(x)) = 1 - sin(x)**2,
{
ring_exp,
},
rw this,
rw ← cos_sq',
norm_num,
end


lemma Trigo_2_239_HRKH_extend(h0 : 1 - tan(5*pi/18) * tan(7*pi/18) ≠ 0) (h1 : cos(7*pi/18) ≠ 0) (h2 : cos(5*pi/18) ≠ 0)  (h3 : cos(7*pi/18)≠ 0) (h4 : cos(5*pi/18)≠ 0) (h5 : tan((7*pi/18)+(5*pi/18))≠ 0) (h6 : 1-tan(7*pi/18)*tan(5*pi/18)≠ 0) (h7 : tan(2*pi/3)≠ 0) (h8 : cos(5*pi/36)≠ 0) (h9 : (1-tan(5*pi/36)**2)≠ 0) (h10 : cos((4*pi/3)/2)≠ 0) (h11 : sin(4*pi/3)≠ 0) (h12 : (1+cos(4*pi/3))≠ 0) (h13 : (sin(4*pi/3)/(1+cos(4*pi/3)))≠ 0) : -sqrt(3)*(1 + (cos(4*pi/3) + 1)*(-tan(7*pi/18) - 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2))/sin(4*pi/3)) + 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2) + tan(7*pi/18)=-sqrt(3):=
begin
have : -sqrt 3 * (1 + (-tan(7 * pi / 18) - 2 * tan(5 * pi / 36) / (1 - tan(5 * pi / 36) ** 2)) / (sin(4 * pi / 3) / (1 + cos(4 * pi / 3)))) + 2 * tan(5 * pi / 36) / (1 - tan(5 * pi / 36) ** 2) + tan(7 * pi / 18) = -sqrt(3)*(1 + (cos(4*pi/3) + 1)*(-tan(7*pi/18) - 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2))/sin(4*pi/3)) + 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2) + tan(7*pi/18),
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
have : -sqrt 3 * (1 + (-tan(7 * pi / 18) - 2 * tan(5 * pi / 36) / (1 - tan(5 * pi / 36) ** 2)) / tan(2 * pi / 3)) + 2 * tan(5 * pi / 36) / (1 - tan(5 * pi / 36) ** 2) + tan(7 * pi / 18) = -sqrt(3)*(1 + (-tan(7*pi/18) - 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2))/tan(2*pi/3)) + 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2) + tan(7*pi/18),
{
field_simp at *,
},
have : tan(5*pi/18) = 2 * tan(5*pi/36) / ( 1 - tan(5*pi/36) ** 2 ),
{
have : tan(5*pi/18) = tan(2*(5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * (-(tan(7 * pi / 18) + tan(5 * pi / 18)) / tan(2 * pi / 3) + 1) + tan(5 * pi / 18) + tan(7 * pi / 18) = -sqrt(3)*(1 + (-tan(7*pi/18) - tan(5*pi/18))/tan(2*pi/3)) + tan(5*pi/18) + tan(7*pi/18),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/18) * tan(5*pi/18) = -( tan(7*pi/18) + tan(5*pi/18) ) / tan(2*pi/3) + 1,
{
rw tan_mul_tan',
have : tan((7*pi/18) + (5*pi/18)) = tan(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -sqrt(3)*(tan(7*pi/18) * tan(5*pi/18)) = -sqrt(3)*tan(5*pi/18)*tan(7*pi/18),
{
ring,
},
conv {to_lhs, rw this,},
rw add_assoc,
have : tan(5*pi/18) + tan(7*pi/18) = (-tan(5*pi/18)*tan(7*pi/18) + 1)*tan(2*pi/3),
{
rw tan_add_tan,
have : tan((5*pi/18) + (7*pi/18)) = tan(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(5*pi/18)*tan(7*pi/18) + 1)*tan(2*pi/3) = tan(2*pi/3) - tan(5*pi/18)*tan(7*pi/18)*tan(2*pi/3),
{
ring_exp,
},
rw this,
have : tan(2*pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_three,
norm_num,
ring_exp,
end


lemma Trigo_2_240_EXWT_extend(h0 : sin(pi/9) ≠ 0) (h1 : sin(pi/9)≠ 0) : (-1/2 + (-sin(3445*pi/72)**2 + cos(3445*pi/36)/2 + 1/2)**2)/sin(pi/9)=-1/2:=
begin
have : ((-1) / 2 + (-sin(3445 * pi / 72) ** 2 + (cos(3445 * pi / 36) / 2 + 1 / 2)) ** 2) / sin(pi / 9) = (-1/2 + (-sin(3445*pi/72)**2 + cos(3445*pi/36)/2 + 1/2)**2)/sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3445*pi/72) ** 2 = cos(3445*pi/36) / 2 + 1 / 2,
{
have : cos(3445*pi/36) = cos(2*(3445*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-1) / 2 + (-sin(3445 * pi / 72) ** 2 + cos(3445 * pi / 72) ** 2) ** 2) / sin(pi / 9) = (-1/2 + (-sin(3445*pi/72)**2 + cos(3445*pi/72)**2)**2)/sin(pi/9),
{
field_simp at *,
},
have : cos(3445*pi/36) = -sin(3445*pi/72) ** 2 + cos(3445*pi/72) ** 2,
{
have : cos(3445*pi/36) = cos(2*(3445*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : (cos(3445 * pi / 36) ** 2 - 1 / 2) / sin(pi / 9) = (-1/2 + cos(3445*pi/36)**2)/sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/36) = cos(3445*pi/36),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/36) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/36)**2 = 1/2 - cos(7*pi/18)/2,
{
have : cos(7*pi/18) = cos(2*(7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(7*pi/18) = sin(pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_241_JCOO_extend(h0 : cos(2*x) ≠ 0) (h1 : sin (2 * x) + cos (2 * x) ≠ 0) (h2 : -sin(2*x) + cos(2*x) ≠ 0)  (h5 : (-(-sin(2*x+35*pi))**2+cos(2*x)**2)≠ 0) (h6 : (-sin(2*x+35*pi)**2+cos(2*x)**2)≠ 0) (h7 : (1+1/tan(-2*x+93*pi/2))≠ 0) (h8 : (1+1/tan((-2)*x+93*pi/2))≠ 0) (h9 : tan(-2*x+93*pi/2)≠ 0) (h10 : tan((-2)*x+93*pi/2)≠ 0) (h11 : ((-sin(2*pi)*sin(2*x-2*pi)+cos(2*pi)*cos(2*x-2*pi))**2-sin(2*x+35*pi)**2)≠ 0) (h12 : (-sin(2*x+35*pi)**2+(-sin(2*x-2*pi)*sin(2*pi)+cos(2*x-2*pi)*cos(2*pi))**2)≠ 0) : (2*(-sin(2*pi)*sin(2*x - 2*pi) + cos(2*pi)*cos(2*x - 2*pi))*sin(2*x + 35*pi) + 1)/((-sin(2*pi)*sin(2*x - 2*pi) + cos(2*pi)*cos(2*x - 2*pi))**2 - sin(2*x + 35*pi)**2)=(1 - 1/tan(-2*x + 93*pi/2))/(1 + 1/tan(-2*x + 93*pi/2)):=
begin
have : (2 * sin(2 * x + 35 * pi) * (-sin(2 * x - 2 * pi) * sin(2 * pi) + cos(2 * x - 2 * pi) * cos(2 * pi)) + 1) / (-sin(2 * x + 35 * pi) ** 2 + (-sin(2 * x - 2 * pi) * sin(2 * pi) + cos(2 * x - 2 * pi) * cos(2 * pi)) ** 2) = (2*(-sin(2*pi)*sin(2*x - 2*pi) + cos(2*pi)*cos(2*x - 2*pi))*sin(2*x + 35*pi) + 1)/((-sin(2*pi)*sin(2*x - 2*pi) + cos(2*pi)*cos(2*x - 2*pi))**2 - sin(2*x + 35*pi)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -sin(2*x - 2*pi) * sin(2*pi) + cos(2*x - 2*pi) * cos(2*pi),
{
have : cos(2*x) = cos((2*x - 2*pi) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - 1 / tan((-2) * x + 93 * pi / 2)) / (1 + 1 / tan((-2) * x + 93 * pi / 2)) = (1 - 1/tan(-2*x + 93*pi/2))/(1 + 1/tan(-2*x + 93*pi/2)),
{
field_simp at *,
},
have : tan(2*x) = 1 / tan(-2*x + 93*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*x) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : ((-2) * -sin(2 * x + 35 * pi) * cos(2 * x) + 1) / (-(-sin(2 * x + 35 * pi)) ** 2 + cos(2 * x) ** 2) = (2*sin(2*x + 35*pi)*cos(2*x) + 1)/(-sin(2*x + 35*pi)**2 + cos(2*x)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*x) = -sin(2*x + 35*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*x) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -2*sin(2*x)*cos(2*x) + 1 = sin(2*x)**2 - 2*sin(2*x)*cos(2*x) + cos(2*x)**2,
{
have : -2*sin(2*x)*cos(2*x) + 1 = -2*sin(2*x)*cos(2*x) + (sin(2*x)**2 + cos(2*x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
ring,
},
rw this,
have : sin(2*x)**2 - 2*sin(2*x)*cos(2*x) + cos(2*x)**2 = (-sin(2*x) + cos(2*x))**2,
{
ring_exp,
},
rw this,
have : -sin(2*x)**2 + cos(2*x)**2 = (-sin(2*x) + cos(2*x))*(sin(2*x) + cos(2*x)),
{
ring_exp,
},
rw this,
rw tan_eq_sin_div_cos,
have : 1 + sin(2*x)/cos(2*x) = (sin(2*x) + cos(2*x))/cos(2*x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : 1 - sin(2*x)/cos(2*x) = (-sin(2*x) + cos(2*x))/cos(2*x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_2_242_LQDW_extend(h0 : 2 - sqrt(3) ≠ 0)  (h1 : cos(11*pi/12)≠ 0) (h2 : cos(pi)≠ 0) (h3 : (tan(11*pi/12)*tan(pi)+1)≠ 0) (h4 : (1+tan(11*pi/12)*tan(pi))≠ 0) (h5 : cos(pi/2)≠ 0) (h6 : (tan(11*pi/12)*(2*tan(pi/2)/(1-tan(pi/2)**2))+1)≠ 0) (h7 : (2*tan(pi/2)*tan(11*pi/12)/(1-tan(pi/2)**2)+1)≠ 0) (h8 : (1-tan(pi/2)**2)≠ 0) (h9 : (1-(-tan(103*pi/2))**2)≠ 0) (h10 : (-2*tan(11*pi/12)*tan(103*pi/2)/(1-tan(103*pi/2)**2)+1)≠ 0) (h11 : (1-tan(103*pi/2)**2)≠ 0) (h12 : (2*-tan(103*pi/2)*tan(11*pi/12)/(1-(-tan(103*pi/2))**2)+1)≠ 0) : tan(7*pi/12) + 1 + (sqrt(3) + 2)*((tan(11*pi/12) + 2*tan(103*pi/2)/(1 - tan(103*pi/2)**2))/(-2*tan(11*pi/12)*tan(103*pi/2)/(1 - tan(103*pi/2)**2) + 1) + 1)=0:=
begin
have : tan(7 * pi / 12) + 1 + (sqrt 3 + 2) * ((tan(11 * pi / 12) - 2 * -tan(103 * pi / 2) / (1 - (-tan(103 * pi / 2)) ** 2)) / (2 * -tan(103 * pi / 2) * tan(11 * pi / 12) / (1 - (-tan(103 * pi / 2)) ** 2) + 1) + 1) = tan(7*pi/12) + 1 + (sqrt(3) + 2)*((tan(11*pi/12) + 2*tan(103*pi/2)/(1 - tan(103*pi/2)**2))/(-2*tan(11*pi/12)*tan(103*pi/2)/(1 - tan(103*pi/2)**2) + 1) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/2) = -tan(103*pi/2),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/2) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7 * pi / 12) + 1 + (sqrt 3 + 2) * ((tan(11 * pi / 12) - 2 * tan(pi / 2) / (1 - tan(pi / 2) ** 2)) / (tan(11 * pi / 12) * (2 * tan(pi / 2) / (1 - tan(pi / 2) ** 2)) + 1) + 1) = tan(7*pi/12) + 1 + (sqrt(3) + 2)*((tan(11*pi/12) - 2*tan(pi/2)/(1 - tan(pi/2)**2))/(2*tan(pi/2)*tan(11*pi/12)/(1 - tan(pi/2)**2) + 1) + 1),
{
field_simp at *,
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
have : tan(7 * pi / 12) + 1 + (2 + sqrt 3) * ((tan(11 * pi / 12) - tan(pi)) / (1 + tan(11 * pi / 12) * tan(pi)) + 1) = tan(7*pi/12) + 1 + (sqrt(3) + 2)*((tan(11*pi/12) - tan(pi))/(tan(11*pi/12)*tan(pi) + 1) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/12) = ( tan(11*pi/12) - tan(pi) ) / ( 1 + tan(11*pi/12) * tan(pi) ),
{
have : tan(-pi/12) = tan((11*pi/12) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/12) = -1/tan(pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7*pi/12) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-pi/12) = -tan(pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_twelve,
field_simp,
ring_exp,
have : -sqrt(3)**3 = -sqrt(3) * sqrt(3)**2,
{
ring,
},
rw this,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_2_243_PTCJ_extend(h0 : sin(pi/11) ≠ 0)  : (sin(-2*pi)*sin(-17*pi/11) + cos(-2*pi)*cos(-17*pi/11))*(sin(2*pi)*sin(24*pi/11) + cos(2*pi)*cos(24*pi/11))*(-sin(pi/22)**2 + cos(pi/22)**2)*cos(3*pi/11)*cos(4*pi/11)=1/2**5:=
begin
have : (sin(2 * pi) * sin(24 * pi / 11) + cos(2 * pi) * cos(24 * pi / 11)) * (-sin(pi / 22) ** 2 + cos(pi / 22) ** 2) * cos(3 * pi / 11) * cos(4 * pi / 11) * (sin((-17) * pi / 11) * sin((-2) * pi) + cos((-17) * pi / 11) * cos((-2) * pi)) = (sin(-2*pi)*sin(-17*pi/11) + cos(-2*pi)*cos(-17*pi/11))*(sin(2*pi)*sin(24*pi/11) + cos(2*pi)*cos(24*pi/11))*(-sin(pi/22)**2 + cos(pi/22)**2)*cos(3*pi/11)*cos(4*pi/11),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/11) = sin(-17*pi/11) * sin(-2*pi) + cos(-17*pi/11) * cos(-2*pi),
{
have : cos(5*pi/11) = cos((-17*pi/11) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi / 22) ** 2 + cos(pi / 22) ** 2) * (sin(24 * pi / 11) * sin(2 * pi) + cos(24 * pi / 11) * cos(2 * pi)) * cos(3 * pi / 11) * cos(4 * pi / 11) * cos(5 * pi / 11) = (sin(2*pi)*sin(24*pi/11) + cos(2*pi)*cos(24*pi/11))*(-sin(pi/22)**2 + cos(pi/22)**2)*cos(3*pi/11)*cos(4*pi/11)*cos(5*pi/11),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/11) = sin(24*pi/11) * sin(2*pi) + cos(24*pi/11) * cos(2*pi),
{
have : cos(2*pi/11) = cos((24*pi/11) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/11) = -sin(pi/22) ** 2 + cos(pi/22) ** 2,
{
have : cos(pi/11) = cos(2*(pi/22)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/11) = sin(2*pi/11)/(2*sin(pi/11)),
{
have : sin(2*pi/11) = sin(2*(pi/11)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
rw div_mul_eq_mul_div,
have : sin(2*pi/11)*cos(2*pi/11) = sin(4*pi/11)/2,
{
have : sin(4*pi/11) = 2*sin(2*pi/11)*cos(2*pi/11),
{
have : sin(4*pi/11) = sin(2*(2*pi/11)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/11)/2/(2*sin(pi/11))*cos(3*pi/11)*cos(4*pi/11) = sin(4*pi/11)*cos(4*pi/11)/2/(2*sin(pi/11))*cos(3*pi/11),
{
ring,
},
rw this,
have : sin(4*pi/11)*cos(4*pi/11) = sin(8*pi/11)/2,
{
have : sin(8*pi/11) = 2*sin(4*pi/11)*cos(4*pi/11),
{
have : sin(8*pi/11) = sin(2*(4*pi/11)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(3*pi/11) = -cos(8*pi/11),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/11) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/11)/2/2/(2*sin(pi/11))*-cos(8*pi/11) = -(sin(8*pi/11)*cos(8*pi/11)/2/2/(2*sin(pi/11))),
{
ring,
},
rw this,
have : sin(8*pi/11)*cos(8*pi/11) = sin(16*pi/11)/2,
{
have : sin(16*pi/11) = 2*sin(8*pi/11)*cos(8*pi/11),
{
have : sin(16*pi/11) = sin(2*(8*pi/11)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(16*pi/11) = -sin(5*pi/11),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (16*pi/11) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -(-sin(5*pi/11)/2/2/2/(2*sin(pi/11)))*cos(5*pi/11) = sin(5*pi/11)*cos(5*pi/11)/2/2/2/(2*sin(pi/11)),
{
ring,
},
rw this,
have : sin(5*pi/11)*cos(5*pi/11) = sin(10*pi/11)/2,
{
have : sin(10*pi/11) = 2*sin(5*pi/11)*cos(5*pi/11),
{
have : sin(10*pi/11) = sin(2*(5*pi/11)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(10*pi/11) = sin(pi/11),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (10*pi/11) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_244_ULZV_extend(h0 : sin(x) ≠ 0) (h1 : tan(x) ≠ 0) (h2 : (sin(-x-pi)*tan(-x-pi))≠ 0) : sin(x + 56*pi)*cos(-x + 153*pi)*tan(pi - x)/(sin(-x - pi)*tan(-x - pi))=-cos(x):=
begin
have : cos(-x + 153 * pi) * sin(x + 56 * pi) * tan(pi - x) / (sin(-x - pi) * tan(-x - pi)) = sin(x + 56*pi)*cos(-x + 153*pi)*tan(pi - x)/(sin(-x - pi)*tan(-x - pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 3*pi/2) = sin(x + 56*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x + 3*pi/2) (27),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 231*pi/2) = cos(-x + 153*pi),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 231*pi/2) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi/2) = sin(-x + 231*pi/2),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (x - pi/2) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - pi/2) = -cos(x),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (x - pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + 3*pi/2) = sin(x),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x + 3*pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(pi - x) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi - x) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-x - pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_245_DXOK_extend (h0 : cos(7*pi/12)≠ 0) (h1 : cos(pi/3)≠ 0) (h2 : (sin(pi)+2*cos(pi/6)*tan(pi/3)-sqrt(3)*tan(pi/6))≠ 0) (h3 : (1+tan(7*pi/12)*tan(pi/3))≠ 0) (h4 : (-sqrt(3)*tan(pi/6)+sin(pi)+2*cos(pi/6)*tan(pi/3))≠ 0) (h5 : (tan(pi/3)*tan(7*pi/12)+1)≠ 0) : ((tan(pi/3) - tan(7*pi/12))/(tan(pi/3)*tan(7*pi/12) + 1) + sin(773*pi/6)*cos(pi/2) - 2*(sin(-pi)*cos(4*pi/3) + sin(4*pi/3)*cos(-pi))*cos(pi))/(-sqrt(3)*tan(pi/6) + sin(pi) + 2*cos(pi/6)*tan(pi/3))=(sqrt(3)-1)/2:=
begin
have : ((tan(pi / 3) - tan(7 * pi / 12)) / (tan(pi / 3) * tan(7 * pi / 12) + 1) + sin(773 * pi / 6) * cos(pi / 2) - 2 * (sin(4 * pi / 3) * cos(-pi) + sin(-pi) * cos(4 * pi / 3)) * cos(pi)) / (-sqrt 3 * tan(pi / 6) + sin(pi) + 2 * cos(pi / 6) * tan(pi / 3)) = ((tan(pi/3) - tan(7*pi/12))/(tan(pi/3)*tan(7*pi/12) + 1) + sin(773*pi/6)*cos(pi/2) - 2*(sin(-pi)*cos(4*pi/3) + sin(4*pi/3)*cos(-pi))*cos(pi))/(-sqrt(3)*tan(pi/6) + sin(pi) + 2*cos(pi/6)*tan(pi/3)),
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
have : (-(tan(7 * pi / 12) - tan(pi / 3)) / (tan(pi / 3) * tan(7 * pi / 12) + 1) + sin(773 * pi / 6) * cos(pi / 2) - 2 * sin(pi / 3) * cos(pi)) / (-sqrt 3 * tan(pi / 6) + sin(pi) + 2 * cos(pi / 6) * tan(pi / 3)) = ((tan(pi/3) - tan(7*pi/12))/(tan(pi/3)*tan(7*pi/12) + 1) + sin(773*pi/6)*cos(pi/2) - 2*sin(pi/3)*cos(pi))/(-sqrt(3)*tan(pi/6) + sin(pi) + 2*cos(pi/6)*tan(pi/3)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(773*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 6) * cos(pi / 2) - 2 * sin(pi / 3) * cos(pi) - (tan(7 * pi / 12) - tan(pi / 3)) / (1 + tan(7 * pi / 12) * tan(pi / 3))) / (sin(pi) + 2 * cos(pi / 6) * tan(pi / 3) - sqrt 3 * tan(pi / 6)) = (-(tan(7*pi/12) - tan(pi/3))/(tan(pi/3)*tan(7*pi/12) + 1) + sin(pi/6)*cos(pi/2) - 2*sin(pi/3)*cos(pi))/(-sqrt(3)*tan(pi/6) + sin(pi) + 2*cos(pi/6)*tan(pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) = ( tan(7*pi/12) - tan(pi/3) ) / ( 1 + tan(7*pi/12) * tan(pi/3) ),
{
have : tan(pi/4) = tan((7*pi/12) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw tan_pi_div_four,
rw sin_pi_div_six,
rw cos_pi_div_two,
rw sin_pi_div_three,
rw cos_pi,
rw tan_pi_div_six,
rw sin_pi,
rw cos_pi_div_six,
rw tan_pi_div_three,
norm_num,
ring_exp,
rw sq_sqrt,
field_simp,
ring,
repeat {linarith},
end


lemma Trigo_2_246_FANN_extend : sin(-x + 158*pi)*cos(-y + 18*pi) + sin(x - y) + sin(y + 6*pi)*cos(x)=0:=
begin
have : - -sin(-x + 158 * pi) * cos(-y + 18 * pi) + sin(x - y) + sin(y + 6 * pi) * cos(x) = sin(-x + 158*pi)*cos(-y + 18*pi) + sin(x - y) + sin(y + 6*pi)*cos(x),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -sin(-x + 158*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (x) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(y) = cos(-y + 18*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (y) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - y) - sin(x) * cos(y) + cos(x) * sin(y + 6 * pi) = -sin(x)*cos(y) + sin(x - y) + sin(y + 6*pi)*cos(x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(y) = sin(y + 6*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (y) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_eq_add_neg,
rw add_assoc,
rw ← neg_mul,
rw mul_comm (cos(x)) (sin(y)),
have : -sin(x)*cos(y) + sin(y)*cos(x) = sin(-x + y),
{
have : sin(-x+y) = sin((y) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(-x + y) = -sin(x - y),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + y) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
end


lemma Trigo_2_247_BOSW_extend : -(1 - 2*sin(pi/24)**2)**2 + sin(347*pi/12)**2=-sqrt(3)/2:=
begin
have : -(-sin(pi / 24) ** 2 + (1 - sin(pi / 24) ** 2)) ** 2 + sin(347 * pi / 12) ** 2 = -(1 - 2*sin(pi/24)**2)**2 + sin(347*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) ** 2 = 1 - sin(pi/24) ** 2,
{
rw cos_sq',
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
have : sin(347 * pi / 12) ** 2 - cos(pi / 12) ** 2 = -cos(pi/12)**2 + sin(347*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(347*pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/12) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_eq_neg_add,
have : -cos(pi/12)**2 + sin(pi/12)**2 = -cos(pi/6),
{
have : cos(pi/6) = -sin(pi/12)**2 + cos(pi/12)**2,
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
linarith,
},
rw this,
rw cos_pi_div_six,
ring_exp,
end


lemma Trigo_2_248_FOFC_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : (sin(-x-pi)*tan(x+pi/2))≠ 0) (h3 : sin(-x-pi)≠ 0) (h4 : (sin(-x-pi)*(1/tan(-x+28*pi)))≠ 0) (h5 : tan(-x+28*pi)≠ 0) (h6 : cos(-x + 28*pi)≠ 0) (h7 : cos(-x + 3*pi/2)≠ 0) (h8 : tan((-x + 28*pi)+(-x + 3*pi/2))≠ 0) (h9 : 1-tan(-x + 28*pi)*tan(-x + 3*pi/2)≠ 0) (h10 : tan((-2)*x+59*pi/2)≠ 0) (h11 : tan(-2*x+59*pi/2)≠ 0) : -((-tan(-x + 3*pi/2) - tan(-x + 28*pi))/tan(-2*x + 59*pi/2) + 1)*sin(pi - x)*cos(x + 59*pi)/sin(-x - pi)=-cos(x):=
begin
have : -(-(tan(-x + 28 * pi) + tan(-x + 3 * pi / 2)) / tan((-2) * x + 59 * pi / 2) + 1) * sin(pi - x) * cos(x + 59 * pi) / sin(-x - pi) = -((-tan(-x + 3*pi/2) - tan(-x + 28*pi))/tan(-2*x + 59*pi/2) + 1)*sin(pi - x)*cos(x + 59*pi)/sin(-x - pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-x + 28*pi) * tan(-x + 3*pi/2) = -( tan(-x + 28*pi) + tan(-x + 3*pi/2) ) / tan(-2*x + 59*pi/2) + 1,
{
rw tan_mul_tan',
have : tan((-x + 28*pi) + (-x + 3*pi/2)) = tan(-2*x + 59*pi/2),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -(tan(-x + 28*pi) * tan(-x + 3*pi/2))*sin(pi - x)*cos(x + 59*pi)/sin(-x - pi) = -sin(pi-x)*cos(x+59*pi)*tan(-x+3*pi/2)*tan(-x+28*pi)/sin(-x-pi),
{
ring,
},
conv {to_lhs, rw this,},
have : -sin(pi - x) * cos(x + 59 * pi) * tan(-x + 3 * pi / 2) / (sin(-x - pi) * (1 / tan(-x + 28 * pi))) = -sin(pi - x)*cos(x + 59*pi)*tan(-x + 3*pi/2)*tan(-x + 28*pi)/sin(-x - pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi/2) = 1 / tan(-x + 28*pi),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (x + pi/2) (28),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) * -cos(x + 59 * pi) * tan(-x + 3 * pi / 2) / (sin(-x - pi) * tan(x + pi / 2)) = -sin(pi - x)*cos(x + 59*pi)*tan(-x + 3*pi/2)/(sin(-x - pi)*tan(x + pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = -cos(x + 59*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x + 2*pi) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x + 3*pi/2) = 1/tan(x),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
repeat {rw tan_eq_sin_div_cos},
have : sin(x + pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x + pi/2) = -sin(x),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_2_249_YOAQ_extend(h0 : sqrt(3) - 1 ≠ 0) (h1 : cos(11*pi/24)≠ 0) (h2 : (1-tan(11*pi/24)**2)≠ 0) (h3 : (2*tan(11*pi/24)/(1-tan(11*pi/24)**2)+1)≠ 0) (h4 : (1-tan(1091*pi/24)**2)≠ 0) (h5 : (2*tan(1091*pi/24)/(1-tan(1091*pi/24)**2)+1)≠ 0) : -sin(pi/9)*sin(11*pi/18) + (-3*cos(-7*pi/54) + 4*cos(-7*pi/54)**3)*cos(pi/9) + (tan(pi/12) + 1)/(2*tan(1091*pi/24)/(1 - tan(1091*pi/24)**2) + 1)=sqrt(3):=
begin
have : -sin(pi / 9) * sin(11 * pi / 18) + ((-3) * cos((-7) * pi / 54) + 4 * cos((-7) * pi / 54) ** 3) * cos(pi / 9) + (tan(pi / 12) + 1) / (2 * tan(1091 * pi / 24) / (1 - tan(1091 * pi / 24) ** 2) + 1) = -sin(pi/9)*sin(11*pi/18) + (-3*cos(-7*pi/54) + 4*cos(-7*pi/54)**3)*cos(pi/9) + (tan(pi/12) + 1)/(2*tan(1091*pi/24)/(1 - tan(1091*pi/24)**2) + 1),
{
field_simp at *,
},
have : tan(11*pi/24) = tan(1091*pi/24),
{
rw tan_eq_tan_add_int_mul_pi (11*pi/24) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 9) * sin(11 * pi / 18) + (4 * cos((-7) * pi / 54) ** 3 - 3 * cos((-7) * pi / 54)) * cos(pi / 9) + (tan(pi / 12) + 1) / (2 * tan(11 * pi / 24) / (1 - tan(11 * pi / 24) ** 2) + 1) = -sin(pi/9)*sin(11*pi/18) + (-3*cos(-7*pi/54) + 4*cos(-7*pi/54)**3)*cos(pi/9) + (tan(pi/12) + 1)/(2*tan(11*pi/24)/(1 - tan(11*pi/24)**2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/18) = 4 * cos(-7*pi/54) ** 3 - 3 * cos(-7*pi/54),
{
have : cos(-7*pi/18) = cos(3*(-7*pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 12) + 1) / (2 * tan(11 * pi / 24) / (1 - tan(11 * pi / 24) ** 2) + 1) - sin(pi / 9) * sin(11 * pi / 18) + cos((-7) * pi / 18) * cos(pi / 9) = -sin(pi/9)*sin(11*pi/18) + cos(-7*pi/18)*cos(pi/9) + (tan(pi/12) + 1)/(2*tan(11*pi/24)/(1 - tan(11*pi/24)**2) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/12) = 2 * tan(11*pi/24) / ( 1 - tan(11*pi/24) ** 2 ),
{
have : tan(11*pi/12) = tan(2*(11*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/18) = sin(7*pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-7*pi/18) = cos(7*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sub_eq_add_neg,
rw add_assoc,
rw ← neg_mul,
rw mul_comm (cos(7*pi/18)) (cos(pi/9)),
have : -sin(pi/9)*sin(7*pi/18) + cos(pi/9)*cos(7*pi/18) = cos(pi/2),
{
have : cos(pi/2) = cos((pi/9) + (7*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_two,
have : tan(11*pi/12) = -tan(pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (11*pi/12) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_twelve,
norm_num,
have : sqrt(3) - 2 + 1 = sqrt(3) - 1,
{
ring,
},
rw this,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_3_250_NCWT_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : sin(x+pi)≠ 0) (h3 : (sin(x+pi)/cos(x+pi))≠ 0) (h4 : sin(x+5*pi/2)≠ 0) (h5 : cos(x+pi)≠ 0) : ((-sin(x/2 - pi/2)**2 + cos(x/2 - pi/2)**2)*cos(-2*pi) + sin(-2*pi)*sin(x - pi))*sin(-x)/sin(x + pi) + (-sin(x/2 - pi/2)**2 + cos(x/2 - pi/2)**2)*cos(x + pi/2)/sin(x + 5*pi/2)=sin(x)-cos(x):=
begin
have : (sin((-2) * pi) * sin(x - pi) + cos((-2) * pi) * (-sin(x / 2 - pi / 2) ** 2 + cos(x / 2 - pi / 2) ** 2)) * sin(-x) / sin(x + pi) + (-sin(x / 2 - pi / 2) ** 2 + cos(x / 2 - pi / 2) ** 2) * cos(x + pi / 2) / sin(x + 5 * pi / 2) = ((-sin(x/2 - pi/2)**2 + cos(x/2 - pi/2)**2)*cos(-2*pi) + sin(-2*pi)*sin(x - pi))*sin(-x)/sin(x + pi) + (-sin(x/2 - pi/2)**2 + cos(x/2 - pi/2)**2)*cos(x + pi/2)/sin(x + 5*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi) = -sin(x/2 - pi/2) ** 2 + cos(x/2 - pi/2) ** 2,
{
have : cos(x - pi) = cos(2*(x/2 - pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x) * (sin(x - pi) * sin((-2) * pi) + cos(x - pi) * cos((-2) * pi)) / sin(x + pi) + cos(x - pi) * cos(x + pi / 2) / sin(x + 5 * pi / 2) = (sin(-2*pi)*sin(x - pi) + cos(-2*pi)*cos(x - pi))*sin(-x)/sin(x + pi) + cos(x - pi)*cos(x + pi/2)/sin(x + 5*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi) = sin(x - pi) * sin(-2*pi) + cos(x - pi) * cos(-2*pi),
{
have : cos(x + pi) = cos((x - pi) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x) / (sin(x + pi) / cos(x + pi)) + cos(x - pi) * cos(x + pi / 2) / sin(x + 5 * pi / 2) = sin(-x)*cos(x + pi)/sin(x + pi) + cos(x - pi)*cos(x + pi/2)/sin(x + 5*pi/2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi) = sin(x + pi) / cos(x + pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
rw tan_eq_sin_div_cos,
have : cos(x - pi) = -cos(x),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x - pi) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + pi/2) = -sin(x),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + 5*pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 5*pi/2) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_251_ZNDS_extend : sin(pi/12)**2 + sqrt(3)*(6*sin(3365*pi/72)*cos(3365*pi/72) - 32*sin(3365*pi/72)**3*cos(3365*pi/72)**3)*sin(pi/12)=1/2:=
begin
have : sin(pi / 12) ** 2 + sqrt 3 * (3 * (2 * sin(3365 * pi / 72) * cos(3365 * pi / 72)) - 4 * (2 * sin(3365 * pi / 72) * cos(3365 * pi / 72)) ** 3) * sin(pi / 12) = sin(pi/12)**2 + sqrt(3)*(6*sin(3365*pi/72)*cos(3365*pi/72) - 32*sin(3365*pi/72)**3*cos(3365*pi/72)**3)*sin(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3365*pi/36) = 2 * sin(3365*pi/72) * cos(3365*pi/72),
{
have : sin(3365*pi/36) = sin(2*(3365*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) ** 2 + sqrt 3 * ((-3) * -sin(3365 * pi / 36) + 4 * (-sin(3365 * pi / 36)) ** 3) * sin(pi / 12) = sin(pi/12)**2 + sqrt(3)*(3*sin(3365*pi/36) - 4*sin(3365*pi/36)**3)*sin(pi/12),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/36) = -sin(3365*pi/36),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/36) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 12) ** 2 + sqrt 3 * sin(pi / 12) * (4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36)) = sin(pi/12)**2 + sqrt(3)*(-3*cos(pi/36) + 4*cos(pi/36)**3)*sin(pi/12),
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
rw sin_pi_div_twelve,
rw cos_pi_div_twelve,
ring_exp,
repeat {rw sq_sqrt},
ring,
rw mul_assoc,
rw ← sqrt_mul,
have : sqrt(6*2) = sqrt(3*4),
{
apply congr_arg,
ring,
},
rw this,
rw sqrt_mul,
have : sqrt(4) = sqrt(2**2),
{
apply congr_arg,
ring,
},
rw this,
rw sqrt_sq,
ring,
repeat {linarith},
end


lemma Trigo_3_252_UKFL_extend(h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0)  (h2 : ((-1+2*cos(pi/48)**2)*sin(pi/24))≠ 0) (h3 : (sin(pi/24)*(2*cos(pi/48)**2-1))≠ 0) (h4 : cos((pi/6)/2)≠ 0) (h5 : (1+cos(pi/6))≠ 0) (h6 : (cos(pi/6)+1)≠ 0) (h7 : sin(pi/48)≠ 0) (h8 : ((-1+2*(sin(pi/24)/(2*sin(pi/48)))**2)*sin(pi/24))≠ 0) (h9 : (2*sin(pi/48)**2)≠ 0) (h10 : ((-1+sin(pi/24)**2/(2*sin(pi/48)**2))*sin(pi/24))≠ 0) (h11 : (2*sin(pi/48))≠ 0) : 2*sin(pi/6)/(cos(pi/6) + 1) + (1 - 2*sin(pi/24)**2)/((-1 + sin(pi/24)**2/(2*sin(pi/48)**2))*sin(pi/24))=8:=
begin
have : 2 * sin(pi / 6) / (cos(pi / 6) + 1) + (1 - 2 * sin(pi / 24) ** 2) / ((-1 + 2 * (sin(pi / 24) / (2 * sin(pi / 48))) ** 2) * sin(pi / 24)) = 2*sin(pi/6)/(cos(pi/6) + 1) + (1 - 2*sin(pi/24)**2)/((-1 + sin(pi/24)**2/(2*sin(pi/48)**2))*sin(pi/24)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/48) = sin(pi/24) / ( 2 * sin(pi/48) ),
{
have : sin(pi/24) = sin(2*(pi/48)),
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
have : 2 * (sin(pi / 6) / (1 + cos(pi / 6))) + (1 - 2 * sin(pi / 24) ** 2) / ((-1 + 2 * cos(pi / 48) ** 2) * sin(pi / 24)) = 2*sin(pi/6)/(cos(pi/6) + 1) + (1 - 2*sin(pi/24)**2)/((-1 + 2*cos(pi/48)**2)*sin(pi/24)),
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
have : -(2 * sin(pi / 24) ** 2 - 1) / (sin(pi / 24) * (2 * cos(pi / 48) ** 2 - 1)) + 2 * tan(pi / 12) = 2*tan(pi/12) + (1 - 2*sin(pi/24)**2)/((-1 + 2*cos(pi/48)**2)*sin(pi/24)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = 2 * cos(pi/48) ** 2 - 1,
{
have : cos(pi/24) = cos(2*(pi/48)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(pi/24)*cos(pi/24) = sin(pi/12)/2,
{
have : sin(pi/12) = 2*sin(pi/24)*cos(pi/24),
{
have : sin(pi/12) = sin(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : 2*sin(pi/24)**2 = 1 - cos(pi/12),
{
have : sin(pi/24)**2 = 1/2 - cos(pi/12)/2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
have : -(1-cos(pi/12) - 1)/(sin(pi/12)/2) + 2*(sin(pi/12)/cos(pi/12)) = 2*sin(pi/12)/cos(pi/12) + 2*cos(pi/12)/sin(pi/12),
{
field_simp,
ring,
},
rw this,
have : 2*sin(pi/12)/cos(pi/12) + 2*cos(pi/12)/sin(pi/12) = (2*sin(pi/12)**2 + 2*cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : 2*sin(pi/12)**2 + 2*cos(pi/12)**2 = 2,
{
have : sin(pi/12)**2 + cos(pi/12)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_3_253_IKHE_extend(h0 : 6 - sqrt(3) ≠ 0) (h1 : (2-(2*cos(pi/24)**2-1)**2)≠ 0) (h2 : (2-(-1+2*cos(pi/24)**2)**2)≠ 0) (h3 : sin(pi/24)≠ 0) (h4 : (2*sin(pi/24))≠ 0) (h5 : (2-(-1+sin(pi/12)**2/(2*sin(pi/24)**2))**2)≠ 0) (h6 : (2*sin(pi/24)**2)≠ 0) (h7 : (2-(-1+2*(sin(pi/12)/(2*sin(pi/24)))**2)**2)≠ 0) : (3 - cos(1009*pi/6))/(2 - (-1 + sin(pi/12)**2/(2*sin(pi/24)**2))**2)=2:=
begin
have : (3 - cos(1009 * pi / 6)) / (2 - (-1 + 2 * (sin(pi / 12) / (2 * sin(pi / 24))) ** 2) ** 2) = (3 - cos(1009*pi/6))/(2 - (-1 + sin(pi/12)**2/(2*sin(pi/24)**2))**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = sin(pi/12) / ( 2 * sin(pi/24) ),
{
have : sin(pi/12) = sin(2*(pi/24)),
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
have : sin(pi/3) = cos(1009*pi/6),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (84),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (3 - sin(pi / 3)) / (2 - (2 * cos(pi / 24) ** 2 - 1) ** 2) = (3 - sin(pi/3))/(2 - (-1 + 2*cos(pi/24)**2)**2),
{
field_simp at *,
repeat {left},
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
have : cos(pi/12)**2 = cos(pi/6)/2 + 1/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
rw cos_pi_div_six,
rw sin_pi_div_three,
have : 2 - (sqrt(3)/2/2 + 1/2) = (6 - sqrt(3))/4,
{
ring,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_3_254_JFVI_extend : (-sin(95*pi/3)*sin(-x + 13*pi/30) + sin(-x + 314*pi/15)*cos(pi/3))*sin(x + 3*pi/20) + sin(-x + pi/10)*cos(x + 3*pi/20)=sqrt(2)/2:=
begin
have : (-sin(95 * pi / 3) * sin(-x + 13 * pi / 30) + cos(pi / 3) * sin(-x + 314 * pi / 15)) * sin(x + 3 * pi / 20) + sin(-x + pi / 10) * cos(x + 3 * pi / 20) = (-sin(95*pi/3)*sin(-x + 13*pi/30) + sin(-x + 314*pi/15)*cos(pi/3))*sin(x + 3*pi/20) + sin(-x + pi/10)*cos(x + 3*pi/20),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 13*pi/30) = sin(-x + 314*pi/15),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-x + 13*pi/30) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/3) = -sin(95*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi / 10) * cos(x + 3 * pi / 20) + sin(x + 3 * pi / 20) * (sin(-x + 13 * pi / 30) * sin(pi / 3) + cos(-x + 13 * pi / 30) * cos(pi / 3)) = (sin(pi/3)*sin(-x + 13*pi/30) + cos(pi/3)*cos(-x + 13*pi/30))*sin(x + 3*pi/20) + sin(-x + pi/10)*cos(x + 3*pi/20),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + pi/10) = sin(-x + 13*pi/30) * sin(pi/3) + cos(-x + 13*pi/30) * cos(pi/3),
{
have : cos(-x + pi/10) = cos((-x + 13*pi/30) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/10)*cos(x + 3*pi/20) + sin(x + 3*pi/20)*cos(-x + pi/10) = sin(pi/4),
{
have : sin(pi/4) = sin((x + 3*pi/20) + (-x + pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add (x + 3*pi/20) (-x + pi/10),
ring,
},
rw this,
rw sin_pi_div_four,
end


lemma Trigo_3_255_PNBN_extend(h0 : sqrt(3) ≠ 0) (h1 : (((-4)*sin((-23)*pi/18)**3+3*sin((-23)*pi/18))*tan((-7)*pi/6))≠ 0) (h2 : ((-4*sin(-23*pi/18)**3+3*sin(-23*pi/18))*tan(-7*pi/6))≠ 0) (h3 : (((-4)*sin((-23)*pi/18)**3+3*sin((-23)*pi/18))*(1/tan(20*pi/3)))≠ 0) (h4 : (-4*sin(-23*pi/18)**3+3*sin(-23*pi/18))≠ 0) (h5 : tan(20*pi/3)≠ 0) (h6 : ((-4)*sin((-23)*pi/18)**3+3*sin((-23)*pi/18))≠ 0) : -cos(-19*pi/3)*cos(-19*pi/6)*tan(20*pi/3)*tan(203*pi/6)/(-4*sin(-23*pi/18)**3 + 3*sin(-23*pi/18))=sqrt(3)/2:=
begin
have : cos((-19) * pi / 3) * cos((-19) * pi / 6) * -tan(203 * pi / 6) * tan(20 * pi / 3) / ((-4) * sin((-23) * pi / 18) ** 3 + 3 * sin((-23) * pi / 18)) = -cos(-19*pi/3)*cos(-19*pi/6)*tan(20*pi/3)*tan(203*pi/6)/(-4*sin(-23*pi/18)**3 + 3*sin(-23*pi/18)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-5*pi/6) = -tan(203*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-5*pi/6) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos((-19) * pi / 3) * cos((-19) * pi / 6) * tan((-5) * pi / 6) / (((-4) * sin((-23) * pi / 18) ** 3 + 3 * sin((-23) * pi / 18)) * (1 / tan(20 * pi / 3))) = cos(-19*pi/3)*cos(-19*pi/6)*tan(-5*pi/6)*tan(20*pi/3)/(-4*sin(-23*pi/18)**3 + 3*sin(-23*pi/18)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-7*pi/6) = 1 / tan(20*pi/3),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-7*pi/6) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos((-19) * pi / 3) * cos((-19) * pi / 6) * tan((-5) * pi / 6) / (((-4) * sin((-23) * pi / 18) ** 3 + 3 * sin((-23) * pi / 18)) * tan((-7) * pi / 6)) = cos(-19*pi/3)*cos(-19*pi/6)*tan(-5*pi/6)/((-4*sin(-23*pi/18)**3 + 3*sin(-23*pi/18))*tan(-7*pi/6)),
{
field_simp at *,
},
have : sin(-23*pi/6) = -4 * sin(-23*pi/18) ** 3 + 3 * sin(-23*pi/18),
{
have : sin(-23*pi/6) = sin(3*(-23*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-19*pi/3) = cos(pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-19*pi/3) (-3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
have : cos(-19*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-19*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
have : tan(-5*pi/6) = -tan(5*pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-5*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(5*pi/6) = -tan(pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (5*pi/6) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_six,
have : sin(-23*pi/6) = -sin(23*pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-23*pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(23*pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (23*pi/6) (2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
have : tan(-7*pi/6) = -tan(pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_257_CCUC_extend : -cos(47*pi/180)*cos(73*pi/180) - sin(1031*pi/6)/2 - sin(12764*pi/45)/2=1/2:=
begin
have : sin(7724*pi/45) = sin(12764*pi/45),
{
rw sin_eq_sin_add_int_mul_two_pi (7724*pi/45) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(47 * pi / 180) * cos(73 * pi / 180) - (sin(7724 * pi / 45) / 2 + sin(1031 * pi / 6) / 2) = -cos(47*pi/180)*cos(73*pi/180) - sin(1031*pi/6)/2 - sin(7724*pi/45)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(30913*pi/180) * cos(17*pi/180) = sin(7724*pi/45) / 2 + sin(1031*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((30913*pi/180) + (17*pi/180)) = sin(1031*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((30913*pi/180) - (17*pi/180)) = sin(7724*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(30913*pi/180) * cos(17*pi/180)) = sin(30913*pi/180)*cos(17*pi/180),
{
ring,
},
have : -sin(30913 * pi / 180) * cos(17 * pi / 180) - cos(47 * pi / 180) * cos(73 * pi / 180) = -cos(47*pi/180)*cos(73*pi/180) - sin(30913*pi/180)*cos(17*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(47*pi/180) = -sin(30913*pi/180),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (47*pi/180) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(73*pi/180) = sin(17*pi/180),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (73*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sub_eq_neg_add,
rw mul_comm,
rw ← neg_mul,
have : -sin(17*pi/180)*cos(47*pi/180) + sin(47*pi/180)*cos(17*pi/180) = sin(pi/6),
{
have : sin(pi/6) = sin((47*pi/180) - (17*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_3_258_LGVG_extend(h0 : sin(pi/18) ≠ 0) (h1 : sqrt(3) ≠ 0) (h2 : sin(pi/9)≠ 0) (h3 : (sin(pi/9)-sin(2*pi/9))≠ 0) (h4 : (2*sin(pi/9))≠ 0) (h5 : (-sin(2*pi/9)+sin(pi/9))≠ 0) (h6 : (-3*sin(2*pi/27)+4*sin(2*pi/27)**3+sin(pi/9))≠ 0) (h7 : (-((-4)*sin(2*pi/27)**3+3*sin(2*pi/27))+sin(pi/9))≠ 0) (h8 : ((-3)*sin(2*pi/27)+4*sin(2*pi/27)**3+sin(pi/9))≠ 0) : (-cos(pi/9)**2 + sin(pi/9)**2 + (-4*sin(2*pi/27)**3 + 3*sin(2*pi/27))/(2*sin(pi/9)))/(-3*sin(2*pi/27) + 4*sin(2*pi/27)**3 + sin(pi/9))=-sqrt(3)/3:=
begin
have : (-(-sin(pi / 9) ** 2 + cos(pi / 9) ** 2) + ((-4) * sin(2 * pi / 27) ** 3 + 3 * sin(2 * pi / 27)) / (2 * sin(pi / 9))) / ((-3) * sin(2 * pi / 27) + 4 * sin(2 * pi / 27) ** 3 + sin(pi / 9)) = (-cos(pi/9)**2 + sin(pi/9)**2 + (-4*sin(2*pi/27)**3 + 3*sin(2*pi/27))/(2*sin(pi/9)))/(-3*sin(2*pi/27) + 4*sin(2*pi/27)**3 + sin(pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = -sin(pi/9) ** 2 + cos(pi/9) ** 2,
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
conv {to_lhs, rw ← this,},
have : (-cos(2 * pi / 9) + ((-4) * sin(2 * pi / 27) ** 3 + 3 * sin(2 * pi / 27)) / (2 * sin(pi / 9))) / (-((-4) * sin(2 * pi / 27) ** 3 + 3 * sin(2 * pi / 27)) + sin(pi / 9)) = (-cos(2*pi/9) + (-4*sin(2*pi/27)**3 + 3*sin(2*pi/27))/(2*sin(pi/9)))/(-3*sin(2*pi/27) + 4*sin(2*pi/27)**3 + sin(pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = -4 * sin(2*pi/27) ** 3 + 3 * sin(2*pi/27),
{
have : sin(2*pi/9) = sin(3*(2*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * pi / 9) / (2 * sin(pi / 9)) - cos(2 * pi / 9)) / (sin(pi / 9) - sin(2 * pi / 9)) = (-cos(2*pi/9) + sin(2*pi/9)/(2*sin(pi/9)))/(-sin(2*pi/9) + sin(pi/9)),
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
rw sub_eq_neg_add,
have : -cos(2*pi/9) + cos(pi/9) = -2*sin(-pi/18)*sin(pi/6),
{
rw neg_add_eq_sub,
rw cos_sub_cos,
have : sin(((pi/9) + (2*pi/9))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/9) - (2*pi/9))/2) = sin(-pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw sin_pi_div_six,
have : sin(-pi/18) = -sin(pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sub_eq_neg_add,
have : -sin(2*pi/9) + sin(pi/9) = 2*sin(-pi/18)*cos(pi/6),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((pi/9) + (2*pi/9))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/9) - (2*pi/9))/2) = sin(-pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(-pi/18) = -sin(pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_3_259_RLOJ_extend(h0 : sin(x) ≠ 0) (h1 : (sin(x+5*pi/2)*sin(2*pi)+cos(x+5*pi/2)*cos(2*pi))≠ 0) (h2 : (sin(2*pi)*sin(x+5*pi/2)+cos(2*pi)*cos(x+5*pi/2))≠ 0) (h3 : (sin(2*pi)*sin(x+5*pi/2)+cos(2*pi)*sin(x+5*pi))≠ 0) (h4 : (sin(2*pi)*sin(x+5*pi/2)+sin(x+5*pi)*cos(2*pi))≠ 0) (h5 : (sin(128*pi)*sin(x+5*pi/2)+sin(x+5*pi)*cos(2*pi))≠ 0) : sin(x + pi)*cos(-x + 2*pi)/(sin(128*pi)*sin(x + 5*pi/2) + sin(x + 5*pi)*cos(2*pi))=cos(x):=
begin
have : sin(2*pi) = sin(128*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) * cos(-x + 2 * pi) / (sin(2 * pi) * sin(x + 5 * pi / 2) + cos(2 * pi) * sin(x + 5 * pi)) = sin(x + pi)*cos(-x + 2*pi)/(sin(2*pi)*sin(x + 5*pi/2) + sin(x + 5*pi)*cos(2*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x + 5*pi/2) = sin(x + 5*pi),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x + 5*pi/2) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) * cos(-x + 2 * pi) / (sin(x + 5 * pi / 2) * sin(2 * pi) + cos(x + 5 * pi / 2) * cos(2 * pi)) = sin(x + pi)*cos(-x + 2*pi)/(sin(2*pi)*sin(x + 5*pi/2) + cos(2*pi)*cos(x + 5*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi/2) = sin(x + 5*pi/2) * sin(2*pi) + cos(x + 5*pi/2) * cos(2*pi),
{
have : cos(x + pi/2) = cos((x + 5*pi/2) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + pi/2) = -sin(x),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
rw div_neg,
field_simp,
ring_exp,
end


lemma Trigo_3_260_LPTS_extend(h0 : sin(pi/36) ≠ 0) (h1 : cos(pi/36) ≠ 0) (h2 : sin(pi/18) ≠ 0) (h3 : sin(pi/9) ≠ 0) (h4 : (sqrt(3)*(2*sin(5*pi/36)*cos(5*pi/36))-cos(5*pi/18))≠ 0) (h5 : tan(pi/36)≠ 0) (h6 : (-cos(5*pi/18)+2*sqrt(3)*sin(5*pi/36)*cos(5*pi/36))≠ 0) (h7 : (-cos(5*pi/18)+2*sqrt(3)*(sin(-2*pi)*cos(77*pi/36)+sin(77*pi/36)*cos(-2*pi))*cos(5*pi/36))≠ 0) (h8 : (-cos(5*pi/18)+2*sqrt(3)*(sin(77*pi/36)*cos((-2)*pi)+sin((-2)*pi)*cos(77*pi/36))*cos(5*pi/36))≠ 0) (h9 : (-cos(5*pi/18)-2*sqrt(3)*(sin(-2*pi)*cos(77*pi/36)+sin(77*pi/36)*cos(-2*pi))*sin(6241*pi/36))≠ 0) (h10 : (-cos(5*pi/18)+2*sqrt(3)*(sin((-2)*pi)*cos(77*pi/36)+sin(77*pi/36)*cos((-2)*pi))*-sin(6241*pi/36))≠ 0) : (1 - cos(pi/9))*(-tan(pi/36) + 1/tan(pi/36))/(-cos(5*pi/18) - 2*sqrt(3)*(sin(-2*pi)*cos(77*pi/36) + sin(77*pi/36)*cos(-2*pi))*sin(6241*pi/36))=1:=
begin
have : (1 - cos(pi / 9)) * (-tan(pi / 36) + 1 / tan(pi / 36)) / (-cos(5 * pi / 18) + 2 * sqrt 3 * (sin((-2) * pi) * cos(77 * pi / 36) + sin(77 * pi / 36) * cos((-2) * pi)) * -sin(6241 * pi / 36)) = (1 - cos(pi/9))*(-tan(pi/36) + 1/tan(pi/36))/(-cos(5*pi/18) - 2*sqrt(3)*(sin(-2*pi)*cos(77*pi/36) + sin(77*pi/36)*cos(-2*pi))*sin(6241*pi/36)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/36) = -sin(6241*pi/36),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/36) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos(pi / 9)) * (-tan(pi / 36) + 1 / tan(pi / 36)) / (-cos(5 * pi / 18) + 2 * sqrt 3 * (sin(77 * pi / 36) * cos((-2) * pi) + sin((-2) * pi) * cos(77 * pi / 36)) * cos(5 * pi / 36)) = (1 - cos(pi/9))*(-tan(pi/36) + 1/tan(pi/36))/(-cos(5*pi/18) + 2*sqrt(3)*(sin(-2*pi)*cos(77*pi/36) + sin(77*pi/36)*cos(-2*pi))*cos(5*pi/36)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/36) = sin(77*pi/36) * cos(-2*pi) + sin(-2*pi) * cos(77*pi/36),
{
have : sin(5*pi/36) = sin((77*pi/36) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - cos(pi / 9)) * (-tan(pi / 36) + 1 / tan(pi / 36)) / (sqrt 3 * (2 * sin(5 * pi / 36) * cos(5 * pi / 36)) - cos(5 * pi / 18)) = (1 - cos(pi/9))*(-tan(pi/36) + 1/tan(pi/36))/(-cos(5*pi/18) + 2*sqrt(3)*sin(5*pi/36)*cos(5*pi/36)),
{
field_simp at *,
repeat {left},
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
rw tan_eq_sin_div_cos,
rw one_div_div,
rw ← neg_div,
have : -sin(pi/36)/cos(pi/36) + cos(pi/36)/sin(pi/36) = (-sin(pi/36)**2 + cos(pi/36)**2)/(sin(pi/36)*cos(pi/36)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three],
ring_exp,
},
rw this,
have : -sin(pi/36)**2 + cos(pi/36)**2 = cos(pi/18),
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
rw this,
have : sin(pi/36)*cos(pi/36) = sin(pi/18)/2,
{
have : sin(pi/18) = 2*sin(pi/36)*cos(pi/36),
{
have : sin(pi/18) = sin(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(5*pi/18) = 2*sin(pi/6)*cos(5*pi/18),
{
field_simp,
},
rw this,
have : sqrt(3)*sin(5*pi/18) = 2*sin(5*pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
rw sub_eq_neg_add (2*sin(5*pi/18)*cos(pi/6)) (2*sin(pi/6)*cos(5*pi/18)),
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/6)*cos(5*pi/18) + 2*sin(5*pi/18)*cos(pi/6) = 2*sin(pi/9),
{
have : sin(pi/9) = -sin(pi/6)*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6),
{
have : sin(pi/9) = sin((5*pi/18) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : 1 - cos(pi/9) = 2*sin(pi/18)**2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : 2*sin(pi/18)**2*(cos(pi/18)/(sin(pi/18)/2))/(2*sin(pi/9)) = 2*sin(pi/18)*cos(pi/18)/sin(pi/9),
{
field_simp,
ring_exp,
},
rw this,
have : 2*sin(pi/18)*cos(pi/18) = sin(pi/9),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
field_simp,
end


lemma Trigo_3_261_OXAZ_extend(h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0)  (h2 : cos(pi/24)≠ 0) (h3 : (2*tan(pi/24)/(1-tan(pi/24)**2))≠ 0) (h4 : (1-tan(pi/24)**2)≠ 0) (h5 : (2*tan(pi/24))≠ 0) (h6 : cos(pi/48)≠ 0) (h7 : (1-(2*tan(pi/48)/(1-tan(pi/48)**2))**2)≠ 0) (h8 : (4*tan(pi/48))≠ 0) (h9 : ((1-tan(pi/48)**2)*(-4*tan(pi/48)**2/(1-tan(pi/48)**2)**2+1))≠ 0) (h10 : (1-tan(pi/48)**2)≠ 0) (h11 : (2*(2*tan(pi/48)/(1-tan(pi/48)**2)))≠ 0) (h12 : ((1-tan(1921*pi/48)**2)*((-4)*tan(1921*pi/48)**2/(1-tan(1921*pi/48)**2)**2+1))≠ 0) (h13 : ((1-tan(1921*pi/48)**2)*(-4*tan(1921*pi/48)**2/(1-tan(1921*pi/48)**2)**2+1))≠ 0) (h14 : (1-tan(1921*pi/48)**2)≠ 0) (h15 : (4*tan(1921*pi/48))≠ 0) : (-1 + 4*tan(1921*pi/48)**2/(1 - tan(1921*pi/48)**2)**2)*(1 - tan(1921*pi/48)**2)/(4*tan(1921*pi/48)) + 4*tan(1921*pi/48)/((1 - tan(1921*pi/48)**2)*(-4*tan(1921*pi/48)**2/(1 - tan(1921*pi/48)**2)**2 + 1))=-2*sqrt(3):=
begin
have : (-1 + 4 * tan(1921 * pi / 48) ** 2 / (1 - tan(1921 * pi / 48) ** 2) ** 2) * (1 - tan(1921 * pi / 48) ** 2) / (4 * tan(1921 * pi / 48)) + 4 * tan(1921 * pi / 48) / ((1 - tan(1921 * pi / 48) ** 2) * ((-4) * tan(1921 * pi / 48) ** 2 / (1 - tan(1921 * pi / 48) ** 2) ** 2 + 1)) = (-1 + 4*tan(1921*pi/48)**2/(1 - tan(1921*pi/48)**2)**2)*(1 - tan(1921*pi/48)**2)/(4*tan(1921*pi/48)) + 4*tan(1921*pi/48)/((1 - tan(1921*pi/48)**2)*(-4*tan(1921*pi/48)**2/(1 - tan(1921*pi/48)**2)**2 + 1)),
{
field_simp at *,
},
have : tan(pi/48) = tan(1921*pi/48),
{
rw tan_eq_tan_add_int_mul_pi (pi/48) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - (2 * tan(pi / 48) / (1 - tan(pi / 48) ** 2)) ** 2) / (2 * (2 * tan(pi / 48) / (1 - tan(pi / 48) ** 2))) + 2 * (2 * tan(pi / 48) / (1 - tan(pi / 48) ** 2)) / (1 - (2 * tan(pi / 48) / (1 - tan(pi / 48) ** 2)) ** 2) = (-1 + 4*tan(pi/48)**2/(1 - tan(pi/48)**2)**2)*(1 - tan(pi/48)**2)/(4*tan(pi/48)) + 4*tan(pi/48)/((1 - tan(pi/48)**2)*(-4*tan(pi/48)**2/(1 - tan(pi/48)**2)**2 + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/24) = 2 * tan(pi/48) / ( 1 - tan(pi/48) ** 2 ),
{
have : tan(pi/24) = tan(2*(pi/48)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : 2 * tan(pi / 24) / (1 - tan(pi / 24) ** 2) - 1 / (2 * tan(pi / 24) / (1 - tan(pi / 24) ** 2)) = -(1 - tan(pi/24)**2)/(2*tan(pi/24)) + 2*tan(pi/24)/(1 - tan(pi/24)**2),
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
rw tan_eq_sin_div_cos,
rw one_div_div,
have : sin(pi/12)/cos(pi/12) - cos(pi/12)/sin(pi/12) = (-cos(pi/12)**2 + sin(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : -cos(pi/12)**2 + sin(pi/12)**2 = -cos(pi/6),
{
have : cos(pi/6) = -sin(pi/12)**2 + cos(pi/12)**2,
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
linarith,
},
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_262_LLVY_extend : -(-sin(2*pi)*cos(16937*pi/180) + sin(16937*pi/180)*cos(2*pi))*sin(1123*pi/180) + sin(253*pi/180)*sin(313*pi/180)=1/2:=
begin
have : -sin(1123 * pi / 180) * (sin(16937 * pi / 180) * cos(2 * pi) - sin(2 * pi) * cos(16937 * pi / 180)) + sin(253 * pi / 180) * sin(313 * pi / 180) = -(-sin(2*pi)*cos(16937*pi/180) + sin(16937*pi/180)*cos(2*pi))*sin(1123*pi/180) + sin(253*pi/180)*sin(313*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(16577*pi/180) = sin(16937*pi/180) * cos(2*pi) - sin(2*pi) * cos(16937*pi/180),
{
have : sin(16577*pi/180) = sin((16937*pi/180) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(16577 * pi / 180) * sin(1123 * pi / 180) + sin(253 * pi / 180) * sin(313 * pi / 180) = -sin(1123*pi/180)*sin(16577*pi/180) + sin(253*pi/180)*sin(313*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(163*pi/180) = sin(16577*pi/180),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (163*pi/180) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(163 * pi / 180) * -sin(1123 * pi / 180) + sin(253 * pi / 180) * sin(313 * pi / 180) = -sin(163*pi/180)*sin(1123*pi/180) + sin(253*pi/180)*sin(313*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(223*pi/180) = -sin(1123*pi/180),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (223*pi/180) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(163*pi/180) = sin(17*pi/180),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (163*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(223*pi/180) = -cos(47*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (223*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(253*pi/180) = -cos(17*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (253*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(313*pi/180) = -sin(47*pi/180),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (313*pi/180) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
repeat {rw mul_neg},
repeat {rw ← neg_mul},
rw neg_neg,
rw mul_comm (cos(17*pi/180)) (sin(47*pi/180)),
have : -sin(17*pi/180)*cos(47*pi/180) + sin(47*pi/180)*cos(17*pi/180) = sin(pi/6),
{
have : sin(pi/6) = sin((47*pi/180) - (17*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_3_263_NSHA_extend(h0 : cos(4*pi/9) ≥ 0)  : sqrt(1 - ((-4*sin(pi/18)**3 + 3*sin(pi/18))*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6))**2)=cos(-pi/2)*cos(-pi/18) + sin(-pi/2)*sin(-pi/18):=
begin
have : sqrt (1 - (((-4) * sin(pi / 18) ** 3 + 3 * sin(pi / 18)) * cos(5 * pi / 18) + sin(5 * pi / 18) * cos(pi / 6)) ** 2) = sqrt(1 - ((-4*sin(pi/18)**3 + 3*sin(pi/18))*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6))**2),
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
have : sqrt (1 - (sin(5 * pi / 18) * cos(pi / 6) + sin(pi / 6) * cos(5 * pi / 18)) ** 2) = sqrt(1 - (sin(pi/6)*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6))**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = sin(5*pi/18) * cos(pi/6) + sin(pi/6) * cos(5*pi/18),
{
have : sin(4*pi/9) = sin((5*pi/18) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 18) * sin(-pi / 2) + cos(-pi / 18) * cos(-pi / 2) = cos(-pi/2)*cos(-pi/18) + sin(-pi/2)*sin(-pi/18),
{
field_simp at *,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(4*pi/9) = sin(-pi/18) * sin(-pi/2) + cos(-pi/18) * cos(-pi/2),
{
have : cos(4*pi/9) = cos((-pi/18) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - sin(4*pi/9)**2 = cos(4*pi/9)**2,
{
rw cos_sq',
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
end


lemma Trigo_3_264_LRYC_extend(h0 : sin(pi/18) - cos(pi/18) ≠ 0) (h1 : -sin(pi/18) + cos(pi/18) ≥ 0) (h2 : sin(pi/18) ≥ 0)  (h3 : (-cos(37*pi/18)+sqrt(1-cos(2717*pi/18)**2))≠ 0) (h4 : (sqrt(1-cos(2717*pi/18)**2)-cos(37*pi/18))≠ 0) : sqrt(-2*(sin(1012*pi/9)*cos(pi/2) + sin(pi/2)*cos(1012*pi/9))*cos(pi/18) + 1)/(-cos(37*pi/18) + sqrt(1 - cos(2717*pi/18)**2))=-1:=
begin
have : sqrt ((-2) * (sin(1012 * pi / 9) * cos(pi / 2) + sin(pi / 2) * cos(1012 * pi / 9)) * cos(pi / 18) + 1) / (-cos(37 * pi / 18) + sqrt (1 - cos(2717 * pi / 18) ** 2)) = sqrt(-2*(sin(1012*pi/9)*cos(pi/2) + sin(pi/2)*cos(1012*pi/9))*cos(pi/18) + 1)/(-cos(37*pi/18) + sqrt(1 - cos(2717*pi/18)**2)),
{
field_simp at *,
},
have : sin(2033*pi/18) = sin(1012*pi/9) * cos(pi/2) + sin(pi/2) * cos(1012*pi/9),
{
have : sin(2033*pi/18) = sin((1012*pi/9) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(2033 * pi / 18) * cos(pi / 18) + 1) / (-cos(37 * pi / 18) + sqrt (1 - cos(2717 * pi / 18) ** 2)) = sqrt(-2*sin(2033*pi/18)*cos(pi/18) + 1)/(-cos(37*pi/18) + sqrt(1 - cos(2717*pi/18)**2)),
{
field_simp at *,
},
have : sin(pi/18) = sin(2033*pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/18) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * cos(pi / 18) + 1) / (sqrt (1 - cos(2717 * pi / 18) ** 2) - cos(37 * pi / 18)) = sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-cos(37*pi/18) + sqrt(1 - cos(2717*pi/18)**2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/18) = cos(2717*pi/18),
{
rw cos_eq_cos_add_int_mul_two_pi (17*pi/18) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(37*pi/18) = cos(pi/18),
{
rw cos_eq_cos_add_int_mul_two_pi (37*pi/18) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(17*pi/18) = -cos(pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -2*sin(pi/18)*cos(pi/18) + 1 = -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 ,
{
rw add_assoc,
rw sin_sq_add_cos_sq,
},
rw this,
have : -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 = (-sin(pi/18) + cos(pi/18))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h1,
rw neg_sq,
rw ← sin_sq,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h2,
field_simp,
ring_exp,
end


lemma Trigo_3_265_MHKB_extend(h0 : 2 ≠ 0) (h1 : 4 ≠ 0)  : sin(x + 371*pi/3)**2 - cos(x)**2 - cos(x + pi/3)**2 + 2=3/2:=
begin
have : (-sin(x + 371 * pi / 3)) ** 2 - cos(x) ** 2 - cos(x + pi / 3) ** 2 + 2 = sin(x + 371*pi/3)**2 - cos(x)**2 - cos(x + pi/3)**2 + 2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x + 2*pi/3) = -sin(x + 371*pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + 2*pi/3) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(x + pi / 3) ** 2 + sin(x + 2 * pi / 3) ** 2 - cos(x) ** 2 + 1 = sin(x + 2*pi/3)**2 - cos(x)**2 - cos(x + pi/3)**2 + 2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/3) ** 2 = 1 - cos(x + pi/3) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(x) ** 2 + sin(x + pi / 3) ** 2 + sin(x + 2 * pi / 3) ** 2 = sin(x + pi/3)**2 + sin(x + 2*pi/3)**2 - cos(x)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) ** 2 = 1 - cos(x) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/3) = sin(x)*cos(pi/3) + sin(pi/3)*cos(x),
{
have : sin(x+pi/3) = sin((x) + (pi/3)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
have : sin(x + 2*pi/3) = sin(x)*cos(2*pi/3) + sin(2*pi/3)*cos(x),
{
have : sin(x+2*pi/3) = sin((x) + (2*pi/3)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(2*pi/3) = sin(pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
have : (sin(x)*-(1/2) + sqrt(3)/2*cos(x))**2 = sin(x)**2/4 - sqrt(3)*sin(x)*cos(x)/2 + 3*cos(x)**2/4,
{
ring_exp,
rw sq_sqrt,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
linarith,
},
rw this,
have : (sin(x)*(1/2) + sqrt(3)/2*cos(x))**2 = sin(x)**2/4 + sqrt(3)*sin(x)*cos(x)/2 + 3*cos(x)**2/4,
{
ring_exp,
rw sq_sqrt,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
linarith,
},
rw this,
ring_exp,
have : sin(x)**2*(3/2) + cos(x)**2*(3/2) = 3/2,
{
have : sin(x)**2 + cos(x)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
end


lemma Trigo_3_266_BEXW_extend(h0 : sin(pi/9) ≠ 0)  : -(-sin(pi/6)*cos(200*pi/9) + sin(200*pi/9)*cos(pi/6))*sin(pi/6)*cos(pi/9)*cos(1505*pi/9)=1/16:=
begin
have : -sin(pi / 6) * (sin(200 * pi / 9) * cos(pi / 6) - sin(pi / 6) * cos(200 * pi / 9)) * cos(pi / 9) * cos(1505 * pi / 9) = -(-sin(pi/6)*cos(200*pi/9) + sin(200*pi/9)*cos(pi/6))*sin(pi/6)*cos(pi/9)*cos(1505*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(397*pi/18) = sin(200*pi/9) * cos(pi/6) - sin(pi/6) * cos(200*pi/9),
{
have : sin(397*pi/18) = sin((200*pi/9) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) * sin(397 * pi / 18) * cos(pi / 9) * -cos(1505 * pi / 9) = -sin(pi/6)*sin(397*pi/18)*cos(pi/9)*cos(1505*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = -cos(1505*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*pi/9) (83),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(397 * pi / 18) * sin(pi / 6) * cos(pi / 9) * cos(2 * pi / 9) = sin(pi/6)*sin(397*pi/18)*cos(pi/9)*cos(2*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = sin(397*pi/18),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/18) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/18) = cos(4*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : cos(4*pi/9)*cos(pi/3)*(sin(2*pi/9)/(2*sin(pi/9)))*cos(2*pi/9) = cos(4*pi/9)*cos(pi/3)*(sin(2*pi/9)*cos(2*pi/9)/(2*sin(pi/9))),
{
field_simp,
ring_exp,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(4*pi/9)*cos(pi/3)*(sin(4*pi/9)/2/(2*sin(pi/9))) = sin(4*pi/9)*cos(4*pi/9)*cos(pi/3)/2/(2*sin(pi/9)),
{
field_simp,
ring_exp,
},
rw this,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_3_267_WSKL_extend : -(sin(-pi)*sin(-11*pi/12) - sin(117*pi/2)*cos(-11*pi/12))**4 + cos(307*pi/12)**4=-sqrt(3)/2:=
begin
have : -(sin(-pi) * sin((-11) * pi / 12) + -sin(117 * pi / 2) * cos((-11) * pi / 12)) ** 4 + cos(307 * pi / 12) ** 4 = -(sin(-pi)*sin(-11*pi/12) - sin(117*pi/2)*cos(-11*pi/12))**4 + cos(307*pi/12)**4,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = -sin(117*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin((-11) * pi / 12) * sin(-pi) + cos((-11) * pi / 12) * cos(-pi)) ** 4 + cos(307 * pi / 12) ** 4 = -(sin(-pi)*sin(-11*pi/12) + cos(-pi)*cos(-11*pi/12))**4 + cos(307*pi/12)**4,
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
have : cos(307 * pi / 12) ** 4 - cos(pi / 12) ** 4 = -cos(pi/12)**4 + cos(307*pi/12)**4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(307*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/12) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12)**4 - cos(pi/12)**4 = (sin(pi/12)**2 - cos(pi/12)**2)*(sin(pi/12)**2 + cos(pi/12)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : sin(pi/12)**2 - cos(pi/12)**2 = -cos(pi/6),
{
have : cos(pi/6) = -sin(pi/12)**2 + cos(pi/12)**2,
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
rw this,
ring,
},
rw this,
rw cos_pi_div_six,
ring,
end


lemma Trigo_3_268_TAEG_extend(h0 : cos(2*pi/45) ≠ 0) (h1 : cos(pi/12) ≠ 0)  (h2 : (-(-sin(-2*pi)*cos(-88*pi/45)+sin(-88*pi/45)*cos(-2*pi))*sin(pi/12)+cos(7*pi/180))≠ 0) (h3 : (-(sin((-88)*pi/45)*cos((-2)*pi)-sin((-2)*pi)*cos((-88)*pi/45))*sin(pi/12)+cos(7*pi/180))≠ 0) (h4 : (-(-sin((-2)*pi)*cos((-88)*pi/45)+sin((-88)*pi/45)*(1-2*sin(-pi)**2))*sin(pi/12)+cos(7*pi/180))≠ 0) (h5 : ((-(1-2*sin(-pi)**2)*sin(-88*pi/45)+sin(-2*pi)*cos(-88*pi/45))*sin(pi/12)+cos(7*pi/180))≠ 0) (h6 : ((-sin(-88*pi/45)*cos(-2*pi)+sin(-2*pi)*cos(-88*pi/45))*sin(pi/12)+cos(7*pi/180))≠ 0) (h7 : ((-(1-2*(1/2-cos((-2)*pi)/2))*sin((-88)*pi/45)+sin((-2)*pi)*cos((-88)*pi/45))*sin(pi/12)+cos(7*pi/180))≠ 0) : (sin(7*pi/180) + (-sin(-2*pi)*cos(-88*pi/45) + sin(-88*pi/45)*cos(-2*pi))*cos(pi/12))/((-sin(-88*pi/45)*cos(-2*pi) + sin(-2*pi)*cos(-88*pi/45))*sin(pi/12) + cos(7*pi/180))=2-sqrt(3):=
begin
have : (sin(7 * pi / 180) + (-sin((-2) * pi) * cos((-88) * pi / 45) + (1 - 2 * (1 / 2 - cos((-2) * pi) / 2)) * sin((-88) * pi / 45)) * cos(pi / 12)) / ((-(1 - 2 * (1 / 2 - cos((-2) * pi) / 2)) * sin((-88) * pi / 45) + sin((-2) * pi) * cos((-88) * pi / 45)) * sin(pi / 12) + cos(7 * pi / 180)) = (sin(7*pi/180) + (-sin(-2*pi)*cos(-88*pi/45) + sin(-88*pi/45)*cos(-2*pi))*cos(pi/12))/((-sin(-88*pi/45)*cos(-2*pi) + sin(-2*pi)*cos(-88*pi/45))*sin(pi/12) + cos(7*pi/180)),
{
field_simp at *,
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
conv {to_lhs, rw ← this,},
have : (sin(7 * pi / 180) + (-sin((-2) * pi) * cos((-88) * pi / 45) + sin((-88) * pi / 45) * (1 - 2 * sin(-pi) ** 2)) * cos(pi / 12)) / (-(-sin((-2) * pi) * cos((-88) * pi / 45) + sin((-88) * pi / 45) * (1 - 2 * sin(-pi) ** 2)) * sin(pi / 12) + cos(7 * pi / 180)) = (sin(7*pi/180) + (-sin(-2*pi)*cos(-88*pi/45) + (1 - 2*sin(-pi)**2)*sin(-88*pi/45))*cos(pi/12))/((-(1 - 2*sin(-pi)**2)*sin(-88*pi/45) + sin(-2*pi)*cos(-88*pi/45))*sin(pi/12) + cos(7*pi/180)),
{
field_simp at *,
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
have : (sin(7 * pi / 180) + (sin((-88) * pi / 45) * cos((-2) * pi) - sin((-2) * pi) * cos((-88) * pi / 45)) * cos(pi / 12)) / (-(sin((-88) * pi / 45) * cos((-2) * pi) - sin((-2) * pi) * cos((-88) * pi / 45)) * sin(pi / 12) + cos(7 * pi / 180)) = (sin(7*pi/180) + (-sin(-2*pi)*cos(-88*pi/45) + sin(-88*pi/45)*cos(-2*pi))*cos(pi/12))/(-(-sin(-2*pi)*cos(-88*pi/45) + sin(-88*pi/45)*cos(-2*pi))*sin(pi/12) + cos(7*pi/180)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/45) = sin(-88*pi/45) * cos(-2*pi) - sin(-2*pi) * cos(-88*pi/45),
{
have : sin(2*pi/45) = sin((-88*pi/45) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/45)*cos(pi/12) = sin(-7*pi/180)/2 + sin(23*pi/180)/2,
{
rw sin_mul_cos,
have : sin((2*pi/45) + (pi/12)) = sin(23*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : sin((2*pi/45) - (pi/12)) = sin(-7*pi/180),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(-7*pi/180) = -sin(7*pi/180),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-7*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw neg_mul,
have : sin(2*pi/45)*sin(pi/12) = -cos(23*pi/180)/2 + cos(-7*pi/180)/2,
{
rw sin_mul_sin,
have : cos((2*pi/45) + (pi/12)) = cos(23*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi/45) - (pi/12)) = cos(-7*pi/180),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(-7*pi/180) = cos(7*pi/180),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/180) + (-sin(7*pi/180)/2 + sin(23*pi/180)/2) = sin(7*pi/180)/2 + sin(23*pi/180)/2,
{
ring,
},
rw this,
have : sin(7*pi/180)/2 + sin(23*pi/180)/2 = sin(pi/12)*cos(2*pi/45),
{
have : sin(7*pi/180) + sin(23*pi/180) = 2*sin(pi/12)*cos(2*pi/45),
{
rw add_comm,
rw sin_add_sin,
have : sin(((23*pi/180) + (7*pi/180))/2) = sin(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((23*pi/180) - (7*pi/180))/2) = cos(2*pi/45),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : -(-cos(23*pi/180)/2 + cos(7*pi/180)/2) + cos(7*pi/180) = cos(23*pi/180)/2 + cos(7*pi/180)/2,
{
ring,
},
rw this,
have : cos(23*pi/180)/2 + cos(7*pi/180)/2 = cos(2*pi/45)*cos(pi/12),
{
have : cos(7*pi/180) + cos(23*pi/180) = 2*cos(2*pi/45)*cos(pi/12),
{
rw add_comm,
rw cos_add_cos,
have : cos(((23*pi/180) + (7*pi/180))/2) = cos(pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((23*pi/180) - (7*pi/180))/2) = cos(2*pi/45),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
have : sin(pi/12)*cos(2*pi/45)/(cos(2*pi/45)*cos(pi/12)) = sin(pi/12)/cos(pi/12),
{
field_simp,
ring,
},
rw this,
rw ← tan_eq_sin_div_cos,
rw tan_pi_div_twelve,
end


lemma Trigo_3_269_GGMF_extend(h0 : cos(x/2) ≠ 0) (h1 : sin(x/2) ≠ 0) (h2 : sin(x) ≠ 0)  (h3 : tan(x/2)≠ 0) : (2*cos(x/2)**2 - 1)*(-2*tan(x/2) + 2/tan(x/2))*sin(-x + 181*pi)=4*cos(x)**2:=
begin
have : (2 * cos(x / 2) ** 2 - 1) * ((-2) * tan(x / 2) + 2 / tan(x / 2)) * sin(-x + 181 * pi) = (2*cos(x/2)**2 - 1)*(-2*tan(x/2) + 2/tan(x/2))*sin(-x + 181*pi),
{
field_simp at *,
},
have : sin(x) = sin(-x + 181*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (x) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (-tan(x / 2) + 1 / tan(x / 2)) * sin(x) * (2 * cos(x / 2) ** 2 - 1) = (2*cos(x/2)**2 - 1)*(-2*tan(x/2) + 2/tan(x/2))*sin(x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = 2 * cos(x/2) ** 2 - 1,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : (-tan(x / 2) + 1 / tan(x / 2)) * (2 * sin(x) * cos(x)) = 2*(-tan(x/2) + 1/tan(x/2))*sin(x)*cos(x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x) = 2 * sin(x) * cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw one_div_div,
have : -(sin(x/2)/cos(x/2)) + cos(x/2)/sin(x/2) = (-sin(x/2)**2 + cos(x/2)**2)/(sin(x/2)*cos(x/2)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : -sin(x/2)**2 + cos(x/2)**2 = cos(x),
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : sin(x/2)*cos(x/2) = sin(x)/2,
{
have : sin(x) = 2*sin(x/2)*cos(x/2),
{
have : sin(x) = sin(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_3_270_MUCD_extend(h0 : cos(11*pi/60) ≠ 0) (h1 : cos(3*pi/20) ≠ 0)  (h2 : cos((3*pi/10)/2)≠ 0) (h3 : ((1-cos(3*pi/10))/sin(3*pi/10)+tan(11*pi/60))≠ 0) (h4 : sin(3*pi/10)≠ 0) (h5 : ((1-cos(3*pi/10))/((-4)*sin(pi/10)**3+3*sin(pi/10))+tan(11*pi/60))≠ 0) (h6 : (-4*sin(pi/10)**3+3*sin(pi/10))≠ 0) (h7 : ((-4)*sin(pi/10)**3+3*sin(pi/10))≠ 0) (h8 : ((1-cos(3*pi/10))/(-4*sin(pi/10)**3+3*sin(pi/10))+tan(11*pi/60))≠ 0) (h9 : (2*sin(3*pi/20)**2/(-4*sin(pi/10)**3+3*sin(pi/10))+tan(11*pi/60))≠ 0) (h10 : ((1-(1-2*sin(3*pi/20)**2))/((-4)*sin(pi/10)**3+3*sin(pi/10))+tan(11*pi/60))≠ 0) : (-2*sin(3*pi/20)**2*tan(11*pi/60)/(-4*sin(pi/10)**3 + 3*sin(pi/10)) + 1)/(2*sin(3*pi/20)**2/(-4*sin(pi/10)**3 + 3*sin(pi/10)) + tan(11*pi/60))=sqrt(3)/3:=
begin
have : ((-1 + (1 - 2 * sin(3 * pi / 20) ** 2)) * tan(11 * pi / 60) / ((-4) * sin(pi / 10) ** 3 + 3 * sin(pi / 10)) + 1) / ((1 - (1 - 2 * sin(3 * pi / 20) ** 2)) / ((-4) * sin(pi / 10) ** 3 + 3 * sin(pi / 10)) + tan(11 * pi / 60)) = (-2*sin(3*pi/20)**2*tan(11*pi/60)/(-4*sin(pi/10)**3 + 3*sin(pi/10)) + 1)/(2*sin(3*pi/20)**2/(-4*sin(pi/10)**3 + 3*sin(pi/10)) + tan(11*pi/60)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/10) = 1 - 2 * sin(3*pi/20) ** 2,
{
have : cos(3*pi/10) = cos(2*(3*pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : (-(1 - cos(3 * pi / 10)) * tan(11 * pi / 60) / ((-4) * sin(pi / 10) ** 3 + 3 * sin(pi / 10)) + 1) / ((1 - cos(3 * pi / 10)) / ((-4) * sin(pi / 10) ** 3 + 3 * sin(pi / 10)) + tan(11 * pi / 60)) = ((-1 + cos(3*pi/10))*tan(11*pi/60)/(-4*sin(pi/10)**3 + 3*sin(pi/10)) + 1)/((1 - cos(3*pi/10))/(-4*sin(pi/10)**3 + 3*sin(pi/10)) + tan(11*pi/60)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/10) = -4 * sin(pi/10) ** 3 + 3 * sin(pi/10),
{
have : sin(3*pi/10) = sin(3*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-((1 - cos(3 * pi / 10)) / sin(3 * pi / 10)) * tan(11 * pi / 60) + 1) / ((1 - cos(3 * pi / 10)) / sin(3 * pi / 10) + tan(11 * pi / 60)) = (-(1 - cos(3*pi/10))*tan(11*pi/60)/sin(3*pi/10) + 1)/((1 - cos(3*pi/10))/sin(3*pi/10) + tan(11*pi/60)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/20) = ( 1 - cos(3*pi/10) ) / sin(3*pi/10),
{
have : tan(3*pi/20) = tan((3*pi/10)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw ← one_div_div,
have : (tan(3*pi/20) + tan(11*pi/60))/(-tan(3*pi/20)*tan(11*pi/60) + 1) = tan(pi/3),
{
have : tan(pi/3) = tan((3*pi/20) + (11*pi/60)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_add,
field_simp,
ring_exp,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
field_simp,
end


lemma Trigo_3_271_VDDH_extend(h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0)  (h2 : -tan(1091*pi/12)≠ 0) (h3 : tan(1091*pi/12)≠ 0) (h4 : cos(1091*pi/24)≠ 0) (h5 : (1-tan(1091*pi/24)**2)≠ 0) (h6 : (2*tan(1091*pi/24))≠ 0) (h7 : (2*tan(1091*pi/24)/(1-tan(1091*pi/24)**2))≠ 0) (h8 : cos(1079*pi/24)≠ 0) (h9 : cos(-pi/2)≠ 0) (h10 : (2*((tan(1079*pi/24)-tan(-pi/2))/(1+tan(1079*pi/24)*tan(-pi/2))))≠ 0) (h11 : (1+tan(-pi/2)*tan(1079*pi/24))≠ 0) (h12 : (1+tan(1079*pi/24)*tan(-pi/2))≠ 0) (h13 : (2*(tan(1079*pi/24)-tan(-pi/2)))≠ 0) (h14 : (1-((tan(1079*pi/24)-tan(-pi/2))/(1+tan(1079*pi/24)*tan(-pi/2)))**2)≠ 0) (h15 : ((1+tan(-pi/2)*tan(1079*pi/24))*(-(tan(1079*pi/24)-tan(-pi/2))**2/(1+tan(-pi/2)*tan(1079*pi/24))**2+1))≠ 0) : 2*(tan(1079*pi/24) - tan(-pi/2))/((1 + tan(-pi/2)*tan(1079*pi/24))*(-(tan(1079*pi/24) - tan(-pi/2))**2/(1 + tan(-pi/2)*tan(1079*pi/24))**2 + 1)) - (1 + tan(-pi/2)*tan(1079*pi/24))*(-(tan(1079*pi/24) - tan(-pi/2))**2/(1 + tan(-pi/2)*tan(1079*pi/24))**2 + 1)/(2*(tan(1079*pi/24) - tan(-pi/2)))=2*sqrt(3):=
begin
have : 2 * ((tan(1079 * pi / 24) - tan(-pi / 2)) / (1 + tan(1079 * pi / 24) * tan(-pi / 2))) / (1 - ((tan(1079 * pi / 24) - tan(-pi / 2)) / (1 + tan(1079 * pi / 24) * tan(-pi / 2))) ** 2) - (1 - ((tan(1079 * pi / 24) - tan(-pi / 2)) / (1 + tan(1079 * pi / 24) * tan(-pi / 2))) ** 2) / (2 * ((tan(1079 * pi / 24) - tan(-pi / 2)) / (1 + tan(1079 * pi / 24) * tan(-pi / 2)))) = 2*(tan(1079*pi/24) - tan(-pi/2))/((1 + tan(-pi/2)*tan(1079*pi/24))*(-(tan(1079*pi/24) - tan(-pi/2))**2/(1 + tan(-pi/2)*tan(1079*pi/24))**2 + 1)) - (1 + tan(-pi/2)*tan(1079*pi/24))*(-(tan(1079*pi/24) - tan(-pi/2))**2/(1 + tan(-pi/2)*tan(1079*pi/24))**2 + 1)/(2*(tan(1079*pi/24) - tan(-pi/2))),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(1091*pi/24) = ( tan(1079*pi/24) - tan(-pi/2) ) / ( 1 + tan(1079*pi/24) * tan(-pi/2) ),
{
have : tan(1091*pi/24) = tan((1079*pi/24) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : 2 * tan(1091 * pi / 24) / (1 - tan(1091 * pi / 24) ** 2) - 1 / (2 * tan(1091 * pi / 24) / (1 - tan(1091 * pi / 24) ** 2)) = 2*tan(1091*pi/24)/(1 - tan(1091*pi/24)**2) - (1 - tan(1091*pi/24)**2)/(2*tan(1091*pi/24)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(1091*pi/12) = 2 * tan(1091*pi/24) / ( 1 - tan(1091*pi/24) ** 2 ),
{
have : tan(1091*pi/12) = tan(2*(1091*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : - -tan(1091 * pi / 12) + 1 / -tan(1091 * pi / 12) = tan(1091*pi/12) - 1/tan(1091*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/12) = -tan(1091*pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/12) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw one_div_div,
rw ← neg_div,
have : -sin(pi/12)/cos(pi/12) + cos(pi/12)/sin(pi/12) = (-sin(pi/12)**2 + cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
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
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw cos_pi_div_six,
rw sin_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_3_272_IFMC_extend(h0 : 2 - sqrt(3) ≠ 0) (h1 : cos(5*pi/12)≠ 0) (h2 : cos(-pi/6)≠ 0) (h3 : (tan(-pi/6)*tan(5*pi/12)+1)≠ 0) (h4 : (1+tan(5*pi/12)*tan(-pi/6))≠ 0) (h5 : cos(5*pi/12)≠ 0) (h6 : cos(-pi/6)≠ 0) (h7 : 1 + tan(5*pi/12) * tan(-pi/6)≠ 0) (h8 : tan(361*pi/12)≠ 0) : -1/tan(361*pi/12)=-2-sqrt(3):=
begin
have : (-1) / tan(361 * pi / 12) = -1/tan(361*pi/12),
{
field_simp at *,
},
have : tan(7*pi/12) = -1 / tan(361*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7*pi/12) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(5 * pi / 12) * tan(-pi / 6) + 1) * tan(7 * pi / 12) / (tan(-pi / 6) * tan(5 * pi / 12) + 1) = tan(7*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/12) - tan(-pi/6) = ( tan(5*pi/12) * tan(-pi/6) + 1 ) * tan(7*pi/12),
{
rw tan_sub_tan,
have : tan((5*pi/12) - (-pi/6)) = tan(7*pi/12),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(5*pi/12) - tan(-pi/6)) = (-tan(-pi/6)+tan(5*pi/12)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan(5 * pi / 12) - tan(-pi / 6)) / (1 + tan(5 * pi / 12) * tan(-pi / 6)) = (-tan(-pi/6) + tan(5*pi/12))/(tan(-pi/6)*tan(5*pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/12) = ( tan(5*pi/12) - tan(-pi/6) ) / ( 1 + tan(5*pi/12) * tan(-pi/6) ),
{
have : tan(7*pi/12) = tan((5*pi/12) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/12) = -1/tan(pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7*pi/12) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_twelve,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_3_273_HDTY_extend(h0 : cos(x) ≠ 0) (h1 : cos(x+135*pi)≠ 0) (h2 : -cos(x+135*pi)≠ 0) (h3 : cos(x+171*pi)≠ 0) : (-sin(-x + 569*pi/6) - cos(x + pi/3))/cos(x + 171*pi)=1:=
begin
have : sin(x + pi/6) = sin(-x + 569*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (x + pi/6) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(x + pi / 6) + cos(x + pi / 3)) / cos(x + 171 * pi) = (-sin(x + pi/6) - cos(x + pi/3))/cos(x + 171*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 135*pi) = cos(x + 171*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (x + 135*pi) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(x + pi / 6) + cos(x + pi / 3)) / -cos(x + 135 * pi) = -(sin(x + pi/6) + cos(x + pi/3))/cos(x + 135*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -cos(x + 135*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/6) = sin(x)*cos(pi/6) + sin(pi/6)*cos(x),
{
have : sin(x+pi/6) = sin((x) + (pi/6)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
have : cos(x + pi/3) = -sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
{
have : cos(x+pi/3) = cos((x) + (pi/3)),
{
apply congr_arg,
ring,
},
rw cos_add,
ring,
},
rw this,
rw sin_pi_div_six,
rw sin_pi_div_three,
rw cos_pi_div_six,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_274_GJQO_extend : (sin(791*pi/12) + sin(5*pi/12))*(-cos(473*pi/12) - cos(1571*pi/12))=sqrt(3)/2:=
begin
have : (sin(791 * pi / 12) + sin(5 * pi / 12)) * (-cos(473 * pi / 12) + -cos(1571 * pi / 12)) = (sin(791*pi/12) + sin(5*pi/12))*(-cos(473*pi/12) - cos(1571*pi/12)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(1571*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/12) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (- -sin(791 * pi / 12) + sin(5 * pi / 12)) * (-cos(473 * pi / 12) + cos(pi / 12)) = (sin(791*pi/12) + sin(5*pi/12))*(-cos(473*pi/12) + cos(pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(791*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi / 12) + sin(5 * pi / 12)) * (cos(pi / 12) + -cos(473 * pi / 12)) = (-sin(pi/12) + sin(5*pi/12))*(-cos(473*pi/12) + cos(pi/12)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = -cos(473*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/12) (19),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi/12) + sin(5*pi/12) = 2*sin(pi/6)*cos(pi/4),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((5*pi/12) + (pi/12))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((5*pi/12) - (pi/12))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw add_comm,
have : cos(5*pi/12) + cos(pi/12) = 2*cos(pi/6)*cos(pi/4),
{
rw cos_add_cos,
have : cos(((5*pi/12) + (pi/12))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((5*pi/12) - (pi/12))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
rw cos_pi_div_four,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_3_275_SIQT_extend : 2*(1 - cos(-2*x - 133*pi))*sin(x/2)*cos(x/2)=sin(2*x)*cos(x):=
begin
have : (1 - cos((-2) * x - 133 * pi)) * (2 * sin(x / 2) * cos(x / 2)) = 2*(1 - cos(-2*x - 133*pi))*sin(x/2)*cos(x/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = 2 * sin(x/2) * cos(x/2),
{
have : sin(x) = sin(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : (1 - cos((-2) * x - 133 * pi)) * sin(x) = (1 - cos(-2*x - 133*pi))*sin(x),
{
field_simp at *,
},
have : cos(2*x + 199*pi) = cos(-2*x - 133*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*x + 199*pi) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(2 * x + 199 * pi) + 1) * sin(x) = (1 - cos(2*x + 199*pi))*sin(x),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -cos(2*x + 199*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*x) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
rw sin_sq,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
norm_num,
ring_exp,
end


lemma Trigo_3_276_BTCL_extend(h0 : -cos(pi/18) + sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≥ 0) (h2 : -cos(pi/18) + sin(pi/18) ≤ 0)  (h3 : (-sqrt(1-sin(17*pi/18)**2)+sin(17*pi/18))≠ 0) (h4 : (-4*sin(17*pi/54)**3-sqrt(1-(-4*sin(17*pi/54)**3+3*sin(17*pi/54))**2)+3*sin(17*pi/54))≠ 0) (h5 : (-sqrt(1-((-4)*sin(17*pi/54)**3+3*sin(17*pi/54))**2)+((-4)*sin(17*pi/54)**3+3*sin(17*pi/54)))≠ 0) (h6 : (4*cos(616*pi/27)**3-sqrt(1-(4*cos(616*pi/27)**3-3*cos(616*pi/27))**2)-3*cos(616*pi/27))≠ 0) (h7 : ((-4)*(-cos(616*pi/27))**3-sqrt(1-((-4)*(-cos(616*pi/27))**3+3*-cos(616*pi/27))**2)+3*-cos(616*pi/27))≠ 0) : sqrt(-2*sin(pi/18)*sin(221*pi/9) + 1)/(4*cos(616*pi/27)**3 - sqrt(1 - (4*cos(616*pi/27)**3 - 3*cos(616*pi/27))**2) - 3*cos(616*pi/27))=-1:=
begin
have : sqrt ((-2) * sin(pi / 18) * sin(221 * pi / 9) + 1) / ((-4) * (-cos(616 * pi / 27)) ** 3 - sqrt (1 - ((-4) * (-cos(616 * pi / 27)) ** 3 + 3 * -cos(616 * pi / 27)) ** 2) + 3 * -cos(616 * pi / 27)) = sqrt(-2*sin(pi/18)*sin(221*pi/9) + 1)/(4*cos(616*pi/27)**3 - sqrt(1 - (4*cos(616*pi/27)**3 - 3*cos(616*pi/27))**2) - 3*cos(616*pi/27)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/54) = -cos(616*pi/27),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (17*pi/54) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * sin(221 * pi / 9) + 1) / (-sqrt (1 - ((-4) * sin(17 * pi / 54) ** 3 + 3 * sin(17 * pi / 54)) ** 2) + ((-4) * sin(17 * pi / 54) ** 3 + 3 * sin(17 * pi / 54))) = sqrt(-2*sin(pi/18)*sin(221*pi/9) + 1)/(-4*sin(17*pi/54)**3 - sqrt(1 - (-4*sin(17*pi/54)**3 + 3*sin(17*pi/54))**2) + 3*sin(17*pi/54)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/18) = -4 * sin(17*pi/54) ** 3 + 3 * sin(17*pi/54),
{
have : sin(17*pi/18) = sin(3*(17*pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * sin(221 * pi / 9) + 1) / (-sqrt (1 - sin(17 * pi / 18) ** 2) + sin(17 * pi / 18)) = sqrt(-2*sin(pi/18)*sin(221*pi/9) + 1)/(-sqrt(1 - sin(17*pi/18)**2) + sin(17*pi/18)),
{
field_simp at *,
},
have : cos(pi/18) = sin(221*pi/9),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/18) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/18) = sin(pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw ← cos_sq',
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h1,
have : -2*sin(pi/18)*cos(pi/18)+1 = -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2,
{
rw add_assoc,
rw sin_sq_add_cos_sq,
},
rw this,
have : -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 = (-cos(pi/18) + sin(pi/18))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h2,
norm_num,
field_simp,
end


lemma Trigo_3_277_LWCL_extend : 2*sin(-pi)*sin(269*pi/6) + 2*cos(-pi)*cos(269*pi/6) - 2*cos(47*pi)=2+sqrt(3):=
begin
have : 2 * (sin(269 * pi / 6) * sin(-pi) + cos(269 * pi / 6) * cos(-pi)) - 2 * cos(47 * pi) = 2*sin(-pi)*sin(269*pi/6) + 2*cos(-pi)*cos(269*pi/6) - 2*cos(47*pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(275*pi/6) = sin(269*pi/6) * sin(-pi) + cos(269*pi/6) * cos(-pi),
{
have : cos(275*pi/6) = cos((269*pi/6) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * (cos(275 * pi / 6) / 2 - cos(47 * pi) / 2) = 2*cos(275*pi/6) - 2*cos(47*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(557*pi/12) * sin(7*pi/12) = cos(275*pi/6) / 2 - cos(47*pi) / 2,
{
rw sin_mul_sin,
have : cos((557*pi/12) + (7*pi/12)) = cos(47*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((557*pi/12) - (7*pi/12)) = cos(275*pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 4*(sin(557*pi/12) * sin(7*pi/12)) = 4*sin(7*pi/12)*sin(557*pi/12),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi/12) = sin(557*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw mul_assoc,
have : sin(7*pi/12)*cos(pi/12) = sin(2*pi/3)/2 + sin(pi/2)/2,
{
rw sin_mul_cos,
have : sin((7*pi/12) + (pi/12)) = sin(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : sin((7*pi/12) - (pi/12)) = sin(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw sin_two_pi_div_three,
rw sin_pi_div_two,
ring_exp,
end


lemma Trigo_3_278_QZBL_extend : (-sin(1407*pi/8) + sin(2133*pi/8))*(-sin(2133*pi/8) - sin(1407*pi/8))=-sqrt(2)/2:=
begin
have : sin(1429*pi/8) = sin(2133*pi/8),
{
rw sin_eq_sin_add_int_mul_two_pi (1429*pi/8) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) = sin(1429*pi/8),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/8) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(1407 * pi / 8) - cos(pi / 8)) * (-sin(1407 * pi / 8) + cos(pi / 8)) = (-sin(1407*pi/8) + cos(pi/8))*(-cos(pi/8) - sin(1407*pi/8)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -sin(1407*pi/8),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/8) (88),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/8) - cos(pi/8))*(sin(pi/8) + cos(pi/8)) = -cos(pi/8)**2 + sin(pi/8)**2,
{
ring_exp,
},
rw this,
have : -cos(pi/8)**2 + sin(pi/8)**2 = -cos(pi/4),
{
have : cos(pi/4) = -sin(pi/8)**2 + cos(pi/8)**2,
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
linarith,
},
rw this,
rw cos_pi_div_four,
ring,
end


lemma Trigo_3_279_WUKR_extend(h0 : cos(4) ≤ 0) (h1 : sin(4) - cos(4) ≤ 0) : 2*sqrt(1 - sin(8)) + sqrt(-2*sin(pi/3)*sin(8 - pi/3) + cos(8 + 74*pi) + cos(8 + 220*pi/3) + 2)=-2*sin(4):=
begin
have : 2 * sqrt (1 - sin(8)) + sqrt ((-2) * sin(pi / 3) * sin(8 - pi / 3) + 2 * (cos(8 + 220 * pi / 3) / 2 + cos(8 + 74 * pi) / 2) + 2) = 2*sqrt(1 - sin(8)) + sqrt(-2*sin(pi/3)*sin(8 - pi/3) + cos(8 + 74*pi) + cos(8 + 220*pi/3) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(8 + 221*pi/3) * cos(pi/3) = cos(8 + 220*pi/3) / 2 + cos(8 + 74*pi) / 2,
{
rw cos_mul_cos,
have : cos((8 + 221*pi/3) + (pi/3)) = cos(8 + 74*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((8 + 221*pi/3) - (pi/3)) = cos(8 + 220*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 2*(cos(8 + 221*pi/3) * cos(pi/3)) = 2*cos(pi/3)*cos(8+221*pi/3),
{
ring,
},
conv {to_lhs, rw this,},
have : 2 * sqrt (1 - sin(8)) + sqrt ((-2) * sin(pi / 3) * sin(8 - pi / 3) + 2 * cos(pi / 3) * cos(8 + 221 * pi / 3) + 2) = 2*sqrt(1 - sin(8)) + sqrt(-2*sin(pi/3)*sin(8 - pi/3) + 2*cos(pi/3)*cos(8 + 221*pi/3) + 2),
{
field_simp at *,
},
have : cos(8 - pi/3) = cos(8 + 221*pi/3),
{
rw cos_eq_cos_add_int_mul_two_pi (8 - pi/3) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sqrt (1 - sin(8)) + sqrt (2 * (-sin(8 - pi / 3) * sin(pi / 3) + cos(8 - pi / 3) * cos(pi / 3)) + 2) = 2*sqrt(1 - sin(8)) + sqrt(-2*sin(pi/3)*sin(8 - pi/3) + 2*cos(pi/3)*cos(8 - pi/3) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(8) = -sin(8 - pi/3) * sin(pi/3) + cos(8 - pi/3) * cos(pi/3),
{
have : cos(8) = cos((8 - pi/3) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8) = 2*sin(4)*cos(4),
{
have : sin(8) = sin(2*(4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : 1 - 2*sin(4)*cos(4) = cos(4)**2 + sin(4)**2 - 2*sin(4)*cos(4),
{
rw cos_sq_add_sin_sq,
},
rw this,
have : cos(4)**2 + sin(4)**2 - 2*sin(4)*cos(4) = (sin(4) - cos(4))**2,
{
ring_exp,
},
rw this,
have : 2 * cos(8) + 2 = 4*cos(4)**2,
{
have : cos(8) + 1 = 2*cos(4)**2,
{
have : cos(8) = cos(2*4),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
linarith,
},
rw this,
rw sqrt_mul,
repeat {rw sqrt_sq_eq_abs},
rw abs_eq_neg_self.mpr h0,
rw abs_eq_neg_self.mpr h1,
have : sqrt(4) = sqrt(2**2),
{
apply congr_arg,
ring,
},
rw this,
rw sqrt_sq,
ring,
repeat {linarith},
end


lemma Trigo_3_280_KWKF_extend(h0 : sin(pi/8) ≠ 0) (h1 : cos(pi/8) ≠ 0)  (h2 : cos(3*pi/8)≠ 0) (h3 : cos(pi/8)≠ 0) (h4 : (cos(3*pi/8)*cos(pi/8))≠ 0) (h5 : (cos(pi/8)*cos(3*pi/8))≠ 0) (h6 : ((-sin(pi/16)**2+cos(pi/16)**2)*cos(3*pi/8))≠ 0) (h7 : ((-1+2*cos(pi/16)**2)*cos(3*pi/8))≠ 0) (h8 : ((-(1-cos(pi/16)**2)+cos(pi/16)**2)*cos(3*pi/8))≠ 0) : sin(pi/4)/((-1 + 2*cos(pi/16)**2)*cos(3*pi/8))=2:=
begin
have : sin(pi / 4) / ((-(1 - cos(pi / 16) ** 2) + cos(pi / 16) ** 2) * cos(3 * pi / 8)) = sin(pi/4)/((-1 + 2*cos(pi/16)**2)*cos(3*pi/8)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/16) ** 2 = 1 - cos(pi/16) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi / 4) / (cos(3 * pi / 8) * cos(pi / 8)) = sin(pi/4)/(cos(pi/8)*cos(3*pi/8)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(3*pi/8) - tan(pi/8) = sin(pi/4) / ( cos(3*pi/8) * cos(pi/8) ),
{
rw tan_sub_tan',
have : sin((3*pi/8) - (pi/8)) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(3*pi/8) - tan(pi/8)) = -tan(pi/8)+tan(3*pi/8),
{
ring,
},
conv {to_lhs, rw this,},
have : tan(3*pi/8) = 1/tan(pi/8),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/8) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
rw one_div_div,
rw ← neg_div,
have : -sin(pi/8)/cos(pi/8) + cos(pi/8)/sin(pi/8) = (-sin(pi/8)**2 + cos(pi/8)**2)/(sin(pi/8)*cos(pi/8)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_eight, -cos_pi_div_eight],
ring_exp,
},
rw this,
have : -sin(pi/8)**2 + cos(pi/8)**2 = cos(pi/4),
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
have : sin(pi/8)*cos(pi/8) = sin(pi/4)/2,
{
have : sin(pi/4) = 2*sin(pi/8)*cos(pi/8),
{
have : sin(pi/4) = sin(2*(pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_3_281_ORXD_extend : -8*(1/2 - cos(pi/12)/2)*cos(pi/24)**2 + 1=sqrt(3)/2:=
begin
have : (-8) * (1 / 2 - cos(pi / 12) / 2) * cos(pi / 24) ** 2 + 1 = -8*(1/2 - cos(pi/12)/2)*cos(pi/24)**2 + 1,
{
field_simp at *,
},
have : sin(pi/24) ** 2 = 1 / 2 - cos(pi/12) / 2,
{
have : cos(pi/12) = cos(2*(pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - 2 * (2 * sin(pi / 24) * cos(pi / 24)) ** 2 = -8*sin(pi/24)**2*cos(pi/24)**2 + 1,
{
field_simp at *,
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
have : 2 * (1 - sin(pi / 12) ** 2) - 1 = 1 - 2*sin(pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) ** 2 = 1 - sin(pi/12) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : 2*cos(pi/12)**2 = cos(pi/6) + 1,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
rw cos_pi_div_six,
ring_exp,
end


lemma Trigo_3_282_UJUW_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : (sin(x+5*pi)*cos(x-pi))≠ 0) (h3 : (sin(x+5*pi)*(1-2*sin(x/2-pi/2)**2))≠ 0) (h4 : ((1-2*sin(x/2-pi/2)**2)*sin(x+5*pi))≠ 0) (h5 : ((1-2*cos(x/2+144*pi)**2)*sin(x+5*pi))≠ 0) (h6 : ((1-2*(-cos(x/2+144*pi))**2)*sin(x+5*pi))≠ 0) : (sin(-2*x + 4*pi)/2 - sin(8*pi)/2)*tan(-x + 2*pi)/((1 - 2*cos(x/2 + 144*pi)**2)*sin(x + 5*pi))=tan(x):=
begin
have : (sin((-2) * x + 4 * pi) / 2 - sin(8 * pi) / 2) * tan(-x + 2 * pi) / ((1 - 2 * (-cos(x / 2 + 144 * pi)) ** 2) * sin(x + 5 * pi)) = (sin(-2*x + 4*pi)/2 - sin(8*pi)/2)*tan(-x + 2*pi)/((1 - 2*cos(x/2 + 144*pi)**2)*sin(x + 5*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(x/2 - pi/2) = -cos(x/2 + 144*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (x/2 - pi/2) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-2) * x + 4 * pi) / 2 - sin(8 * pi) / 2) * tan(-x + 2 * pi) / (sin(x + 5 * pi) * (1 - 2 * sin(x / 2 - pi / 2) ** 2)) = (sin(-2*x + 4*pi)/2 - sin(8*pi)/2)*tan(-x + 2*pi)/((1 - 2*sin(x/2 - pi/2)**2)*sin(x + 5*pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi) = 1 - 2 * sin(x/2 - pi/2) ** 2,
{
have : cos(x - pi) = cos(2*(x/2 - pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : (-sin(8 * pi) / 2 + sin((-2) * x + 4 * pi) / 2) * tan(-x + 2 * pi) / (sin(x + 5 * pi) * cos(x - pi)) = (sin(-2*x + 4*pi)/2 - sin(8*pi)/2)*tan(-x + 2*pi)/(sin(x + 5*pi)*cos(x - pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x - 2*pi) * cos(-x + 6*pi) = -sin(8*pi) / 2 + sin(-2*x + 4*pi) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((-x + 6*pi) + (-x - 2*pi)) = sin(-2*x + 4*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-x + 6*pi) - (-x - 2*pi)) = sin(8*pi),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-x - 2*pi) * cos(-x + 6*pi))*tan(-x + 2*pi)/(sin(x + 5*pi)*cos(x - pi)) = sin(-x-2*pi)*cos(-x+6*pi)*tan(-x+2*pi)/(sin(x+5*pi)*cos(x-pi)),
{
ring,
},
have : sin(-x - 2*pi) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x - 2*pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 6*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 6*pi) (3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-x + 2*pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x + 2*pi) (2),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(x + 5*pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + 5*pi) (-3),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x - pi) = cos(pi - x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x - pi) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(pi - x) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_283_GBSP_extend (h0 : cos(181*pi/180)≠ 0) (h1 : (2*cos(181*pi/180))≠ 0) : -sin(119*pi/180)*sin(181*pi/90)/(2*cos(181*pi/180)) + cos(-13891*pi/90)/2 - cos(464*pi/3)/2=1/2:=
begin
have : -sin(119 * pi / 180) * (sin(181 * pi / 90) / (2 * cos(181 * pi / 180))) + cos((-13891) * pi / 90) / 2 - cos(464 * pi / 3) / 2 = -sin(119*pi/180)*sin(181*pi/90)/(2*cos(181*pi/180)) + cos(-13891*pi/90)/2 - cos(464*pi/3)/2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(181*pi/180) = sin(181*pi/90) / ( 2 * cos(181*pi/180) ),
{
have : sin(181*pi/90) = sin(2*(181*pi/180)),
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
have : -sin(119 * pi / 180) * sin(181 * pi / 180) + (cos((-13891) * pi / 90) / 2 - cos(464 * pi / 3) / 2) = -sin(119*pi/180)*sin(181*pi/180) + cos(-13891*pi/90)/2 - cos(464*pi/3)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(29*pi/180) * sin(27811*pi/180) = cos(-13891*pi/90) / 2 - cos(464*pi/3) / 2,
{
rw sin_mul_sin,
have : cos((29*pi/180) + (27811*pi/180)) = cos(464*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((29*pi/180) - (27811*pi/180)) = cos(-13891*pi/90),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(29*pi/180) * sin(27811*pi/180)) = sin(29*pi/180)*sin(27811*pi/180),
{
ring,
},
have : sin(29 * pi / 180) * sin(27811 * pi / 180) - sin(119 * pi / 180) * sin(181 * pi / 180) = -sin(119*pi/180)*sin(181*pi/180) + sin(29*pi/180)*sin(27811*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(91*pi/180) = sin(27811*pi/180),
{
rw sin_eq_sin_add_int_mul_two_pi (91*pi/180) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_eq_neg_add,
rw ← neg_mul,
have : -sin(119*pi/180)*sin(181*pi/180) = -cos(31*pi/90)/2 + cos(5*pi/3)/2,
{
have : sin(119*pi/180)*sin(181*pi/180) = cos(31*pi/90)/2 - cos(5*pi/3)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((181*pi/180) + (119*pi/180)) = cos(5*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((181*pi/180) - (119*pi/180)) = cos(31*pi/90),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : sin(29*pi/180)*sin(91*pi/180) = cos(31*pi/90)/2 - cos(2*pi/3)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((91*pi/180) + (29*pi/180)) = cos(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos((91*pi/180) - (29*pi/180)) = cos(31*pi/90),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : cos(5*pi/3) = cos(pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(2*pi/3) = -cos(pi/3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_284_OVUD_extend(h0 : 2 ≠ 0) (h1 : sin(x) + cos(x) ≠ 0) (h2 : cos(x) ≠ 0)  (h3 : (sin(2*x)+4*cos(2*x/3)**3-3*cos(2*x/3)+1)≠ 0) (h4 : (sin(2*x)+(4*cos(2*x/3)**3-3*cos(2*x/3))+1)≠ 0) (h5 : (sin(2*x)+4*(-sin(2*x/3+67*pi/2))**3-3*-sin(2*x/3+67*pi/2)+1)≠ 0) (h6 : (sin(2*x)-4*sin(2*x/3+67*pi/2)**3+3*sin(2*x/3+67*pi/2)+1)≠ 0) : (sin(2*x) + 1)/(sin(2*x) - 4*sin(2*x/3 + 67*pi/2)**3 + 3*sin(2*x/3 + 67*pi/2) + 1)=tan(x + 32*pi)/2 + 1/2:=
begin
have : (sin(2 * x) + 1) / (sin(2 * x) + 4 * (-sin(2 * x / 3 + 67 * pi / 2)) ** 3 - 3 * -sin(2 * x / 3 + 67 * pi / 2) + 1) = (sin(2*x) + 1)/(sin(2*x) - 4*sin(2*x/3 + 67*pi/2)**3 + 3*sin(2*x/3 + 67*pi/2) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x/3) = -sin(2*x/3 + 67*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*x/3) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * x) + 1) / (sin(2 * x) + (4 * cos(2 * x / 3) ** 3 - 3 * cos(2 * x / 3)) + 1) = (sin(2*x) + 1)/(sin(2*x) + 4*cos(2*x/3)**3 - 3*cos(2*x/3) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = 4 * cos(2*x/3) ** 3 - 3 * cos(2*x/3),
{
have : cos(2*x) = cos(3*(2*x/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : 1 / 2 * tan(x + 32 * pi) + 1 / 2 = tan(x + 32*pi)/2 + 1/2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(x) = tan(x + 32*pi),
{
rw tan_eq_tan_add_int_mul_pi (x) (32),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_rhs, rw ← this,},
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
have : 2*sin(x)*cos(x) + 1 = 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2,
{
rw add_assoc,
rw sin_sq_add_cos_sq,
},
rw this,
rw add_assoc (2*sin(x)*cos(x)) (cos(2*x)) 1,
have : cos(2*x) + 1 = 2*cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
rw this,
have : 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2 = (sin(x) + cos(x))**2,
{
ring_exp,
},
rw this,
have : 2*sin(x)*cos(x) + 2*cos(x)**2 = 2*(sin(x) + cos(x))*cos(x),
{
ring_exp,
},
rw this,
have : (sin(x) + cos(x))**2/(2*(sin(x) + cos(x))*cos(x)) = (sin(x) + cos(x))/(2*cos(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring_exp,
end


lemma Trigo_3_286_JAKW_extend : sin(5*pi/36)*sin(766*pi/9) + (sin(-pi/6)*sin(2807*pi/18) + cos(-pi/6)*cos(2807*pi/18))*sin(13*pi/36)=sqrt(2)/2:=
begin
have : sin(5 * pi / 36) * sin(766 * pi / 9) + sin(13 * pi / 36) * (sin(2807 * pi / 18) * sin(-pi / 6) + cos(2807 * pi / 18) * cos(-pi / 6)) = sin(5*pi/36)*sin(766*pi/9) + (sin(-pi/6)*sin(2807*pi/18) + cos(-pi/6)*cos(2807*pi/18))*sin(13*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1405*pi/9) = sin(2807*pi/18) * sin(-pi/6) + cos(2807*pi/18) * cos(-pi/6),
{
have : cos(1405*pi/9) = cos((2807*pi/18) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = cos(1405*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : - -sin(766 * pi / 9) * sin(5 * pi / 36) + sin(13 * pi / 36) * sin(7 * pi / 18) = sin(5*pi/36)*sin(766*pi/9) + sin(13*pi/36)*sin(7*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = -sin(766*pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/9) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw neg_mul,
have : sin(pi/9)*sin(5*pi/36) = -cos(pi/4)/2 + cos(pi/36)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((5*pi/36) + (pi/9)) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((5*pi/36) - (pi/9)) = cos(pi/36),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(13*pi/36)*sin(7*pi/18) = -cos(3*pi/4)/2 + cos(pi/36)/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((7*pi/18) + (13*pi/36)) = cos(3*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((7*pi/18) - (13*pi/36)) = cos(pi/36),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(3*pi/4) = -cos(pi/4),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_287_YBFG_extend(h0 : -1 + sqrt(3) ≠ 0) (h1 : cos((13*pi/6)/2)≠ 0) (h2 : (tan(-pi/12)+1)≠ 0) (h3 : sin(13*pi/6)≠ 0) (h4 : cos(181*pi/3)≠ 0) (h5 : (-3*cos(181*pi/9)+4*cos(181*pi/9)**3)≠ 0) (h6 : (4*cos(181*pi/9)**3-3*cos(181*pi/9))≠ 0) : ((1 - cos(13*pi/6))/(-3*cos(181*pi/9) + 4*cos(181*pi/9)**3) + 1)/(tan(-pi/12) + 1)=sqrt(3):=
begin
have : ((1 - cos(13 * pi / 6)) / (4 * cos(181 * pi / 9) ** 3 - 3 * cos(181 * pi / 9)) + 1) / (tan(-pi / 12) + 1) = ((1 - cos(13*pi/6))/(-3*cos(181*pi/9) + 4*cos(181*pi/9)**3) + 1)/(tan(-pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(181*pi/3) = 4 * cos(181*pi/9) ** 3 - 3 * cos(181*pi/9),
{
have : cos(181*pi/3) = cos(3*(181*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/6) = cos(181*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/6) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(13*pi/12) = ( 1 - cos(13*pi/6) ) / sin(13*pi/6),
{
have : tan(13*pi/12) = tan((13*pi/6)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(13*pi/12) = tan(pi/12),
{
rw tan_eq_tan_add_int_mul_pi (13*pi/12) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-pi/12) = -tan(pi/12),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_twelve,
ring_exp,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_3_288_XIPK_extend : (4*cos(1489*pi/36)**3 - 3*cos(1489*pi/36))*cos(pi/6)*cos(797*pi/12)=sqrt(3)/8:=
begin
have : cos(pi / 6) * cos(797 * pi / 12) * (4 * cos(1489 * pi / 36) ** 3 - 3 * cos(1489 * pi / 36)) = (4*cos(1489*pi/36)**3 - 3*cos(1489*pi/36))*cos(pi/6)*cos(797*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1489*pi/12) = 4 * cos(1489*pi/36) ** 3 - 3 * cos(1489*pi/36),
{
have : cos(1489*pi/12) = cos(3*(1489*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(1489 * pi / 12) * cos(pi / 6) * cos(797 * pi / 12) = cos(pi/6)*cos(797*pi/12)*cos(1489*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = cos(1489*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(797 * pi / 12) * sin(5 * pi / 12) * cos(pi / 6) = sin(5*pi/12)*cos(pi/6)*cos(797*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(797*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
field_simp,
left,
ring,
end


lemma Trigo_3_289_UNJI_extend : cos(7*pi/36)*cos(4*pi/9) + cos(-133*pi/36)*cos(pi/18)=sqrt(2)/2:=
begin
have : cos(7 * pi / 36) * cos(4 * pi / 9) - -cos((-133) * pi / 36) * cos(pi / 18) = cos(7*pi/36)*cos(4*pi/9) + cos(-133*pi/36)*cos(pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-1231*pi/36) = -cos(-133*pi/36),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (-1231*pi/36) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7 * pi / 36) * cos(4 * pi / 9) - sin((-1231) * pi / 36) * cos(pi / 18) = cos(7*pi/36)*cos(4*pi/9) - sin(-1231*pi/36)*cos(pi/18),
{
field_simp at *,
},
have : sin(2419*pi/36) = sin(-1231*pi/36),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2419*pi/36) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 18) * -sin(2419 * pi / 36) + cos(7 * pi / 36) * cos(4 * pi / 9) = cos(7*pi/36)*cos(4*pi/9) - sin(2419*pi/36)*cos(pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/36) = -sin(2419*pi/36),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (11*pi/36) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = sin(4*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(11*pi/36) = sin(7*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_comm (sin(4*pi/9)) (sin(7*pi/36)),
have : cos(7*pi/36)*cos(4*pi/9) + sin(7*pi/36)*sin(4*pi/9) = cos(-pi/4),
{
have : cos(-pi/4) = cos((7*pi/36) - (4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
},
rw this,
have : cos(-pi/4) = cos(pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_3_290_LCWZ_extend : -cos(421*pi/12)**2 - sin(1919*pi/12)*cos(5*pi/12) + cos(5*pi/12)**2 + 1=3/2-3*sqrt(3)/4:=
begin
have : -cos(421 * pi / 12) ** 2 + -sin(1919 * pi / 12) * cos(5 * pi / 12) + cos(5 * pi / 12) ** 2 + 1 = -cos(421*pi/12)**2 - sin(1919*pi/12)*cos(5*pi/12) + cos(5*pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -sin(1919*pi/12),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (pi/12) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(-cos(421 * pi / 12)) ** 2 + sin(pi / 12) * cos(5 * pi / 12) + cos(5 * pi / 12) ** 2 + 1 = -cos(421*pi/12)**2 + sin(pi/12)*cos(5*pi/12) + cos(5*pi/12)**2 + 1,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(421*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(pi / 12) ** 2 + sin(pi / 12) * cos(5 * pi / 12) + cos(5 * pi / 12) ** 2 = -cos(pi/12)**2 + sin(pi/12)*cos(5*pi/12) + cos(5*pi/12)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) ** 2 = 1 - cos(pi/12) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/12)**2 + sin(pi/12)*sin(pi/12) + sin(pi/12)**2 = 3*sin(pi/12)**2,
{
ring,
},
rw this,
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
rw cos_pi_div_six,
ring_exp,
end


lemma Trigo_3_291_TZIP_extend : (-4*(-1 + 2*cos(7*pi/360)**2)**3 - 3 + 6*cos(7*pi/360)**2)*sin(9*pi/20) + (1 - 2*sin(9*pi/40)**2)*sin(7*pi/60)=-sqrt(3)/2:=
begin
have : ((-4) * (2 * cos(7 * pi / 360) ** 2 - 1) ** 3 + 3 * (2 * cos(7 * pi / 360) ** 2 - 1)) * sin(9 * pi / 20) + (1 - 2 * sin(9 * pi / 40) ** 2) * sin(7 * pi / 60) = (-4*(-1 + 2*cos(7*pi/360)**2)**3 - 3 + 6*cos(7*pi/360)**2)*sin(9*pi/20) + (1 - 2*sin(9*pi/40)**2)*sin(7*pi/60),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/180) = 2 * cos(7*pi/360) ** 2 - 1,
{
have : cos(7*pi/180) = cos(2*(7*pi/360)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -((-3) * cos(7 * pi / 180) + 4 * cos(7 * pi / 180) ** 3) * sin(9 * pi / 20) + sin(7 * pi / 60) * (1 - 2 * sin(9 * pi / 40) ** 2) = (-4*cos(7*pi/180)**3 + 3*cos(7*pi/180))*sin(9*pi/20) + (1 - 2*sin(9*pi/40)**2)*sin(7*pi/60),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(9*pi/20) = 1 - 2 * sin(9*pi/40) ** 2,
{
have : cos(9*pi/20) = cos(2*(9*pi/40)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 60) * cos(9 * pi / 20) - sin(9 * pi / 20) * (4 * cos(7 * pi / 180) ** 3 - 3 * cos(7 * pi / 180)) = -(-3*cos(7*pi/180) + 4*cos(7*pi/180)**3)*sin(9*pi/20) + sin(7*pi/60)*cos(9*pi/20),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/60) = 4 * cos(7*pi/180) ** 3 - 3 * cos(7*pi/180),
{
have : cos(7*pi/60) = cos(3*(7*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
rw sub_eq_neg_add,
rw ← neg_mul,
have : -sin(9*pi/20)*cos(7*pi/60) + sin(7*pi/60)*cos(9*pi/20) = sin(-pi/3),
{
have : sin(-pi/3) = sin((7*pi/60) - (9*pi/20)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(-pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
ring_exp,
end


lemma Trigo_3_292_OKQD_extend : (-1 + 2*sin(4405*pi/24)**2)*(-3*sin(pi/36) + 4*sin(pi/36)**3) + (-4*sin(pi/36)**3 + 3*sin(pi/36))**2 + (-1 + 2*sin(4405*pi/24)**2)**2=3/4:=
begin
have : (-1 + 2 * (-sin(4405 * pi / 24)) ** 2) * ((-3) * sin(pi / 36) + 4 * sin(pi / 36) ** 3) + ((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) ** 2 + (-1 + 2 * (-sin(4405 * pi / 24)) ** 2) ** 2 = (-1 + 2*sin(4405*pi/24)**2)*(-3*sin(pi/36) + 4*sin(pi/36)**3) + (-4*sin(pi/36)**3 + 3*sin(pi/36))**2 + (-1 + 2*sin(4405*pi/24)**2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/24) = -sin(4405*pi/24),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/24) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) * (2 * cos(pi / 24) ** 2 - 1) + ((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) ** 2 + (2 * cos(pi / 24) ** 2 - 1) ** 2 = (-1 + 2*cos(pi/24)**2)*(-3*sin(pi/36) + 4*sin(pi/36)**3) + (-4*sin(pi/36)**3 + 3*sin(pi/36))**2 + (-1 + 2*cos(pi/24)**2)**2,
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
have : ((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) ** 2 - ((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) * cos(pi / 12) + cos(pi / 12) ** 2 = -(-4*sin(pi/36)**3 + 3*sin(pi/36))*cos(pi/12) + (-4*sin(pi/36)**3 + 3*sin(pi/36))**2 + cos(pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
rw sub_add_eq_add_sub,
rw sin_sq_add_cos_sq,
have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
{
have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
{
have : sin(pi/6) = sin(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_3_293_QSOH_extend(h0 : sin(7*pi/18) ≠ 0)  (h1 : (sin(7*pi/36)*sin(11*pi/36))≠ 0) (h2 : (sin(7*pi/36)*sin(4763*pi/36))≠ 0) : (sin(pi)*sin(1433*pi/9) + sin(pi/18) + cos(pi)*cos(1433*pi/9))/(sin(7*pi/36)*sin(4763*pi/36))=2:=
begin
have : (sin(pi / 18) + (sin(1433 * pi / 9) * sin(pi) + cos(1433 * pi / 9) * cos(pi))) / (sin(7 * pi / 36) * sin(4763 * pi / 36)) = (sin(pi)*sin(1433*pi/9) + sin(pi/18) + cos(pi)*cos(1433*pi/9))/(sin(7*pi/36)*sin(4763*pi/36)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1424*pi/9) = sin(1433*pi/9) * sin(pi) + cos(1433*pi/9) * cos(pi),
{
have : cos(1424*pi/9) = cos((1433*pi/9) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/36) = sin(4763*pi/36),
{
rw sin_eq_sin_add_int_mul_two_pi (11*pi/36) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = cos(1424*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) + sin(5*pi/18) = 2*sin(pi/6)*cos(-pi/9),
{
rw sin_add_sin,
have : sin(((pi/18) + (5*pi/18))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/18) - (5*pi/18))/2) = cos(-pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : cos(-pi/9) = sin(7*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(11*pi/36) = cos(7*pi/36),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/36)*cos(7*pi/36) = sin(7*pi/18)/2,
{
have : sin(7*pi/18) = 2*sin(7*pi/36)*cos(7*pi/36),
{
have : sin(7*pi/18) = sin(2*(7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_294_IBCI_extend(h0 : sin(pi/9) ≠ 0) (h1 : sin(pi/9)≠ 0) : (-sin(-2*pi)*sin(37*pi/18) + cos(-2*pi)*cos(37*pi/18))*(-6*cos(2*pi/27)**2 + 4*(-1 + 2*cos(2*pi/27)**2)**3 + 3)/sin(pi/9)=1/2:=
begin
have : (-sin((-2) * pi) * sin(37 * pi / 18) + cos((-2) * pi) * cos(37 * pi / 18)) * ((-3) * (2 * cos(2 * pi / 27) ** 2 - 1) + 4 * (2 * cos(2 * pi / 27) ** 2 - 1) ** 3) / sin(pi / 9) = (-sin(-2*pi)*sin(37*pi/18) + cos(-2*pi)*cos(37*pi/18))*(-6*cos(2*pi/27)**2 + 4*(-1 + 2*cos(2*pi/27)**2)**3 + 3)/sin(pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/27) = 2 * cos(2*pi/27) ** 2 - 1,
{
have : cos(4*pi/27) = cos(2*(2*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : ((-3) * cos(4 * pi / 27) + 4 * cos(4 * pi / 27) ** 3) * (-sin(37 * pi / 18) * sin((-2) * pi) + cos(37 * pi / 18) * cos((-2) * pi)) / sin(pi / 9) = (-sin(-2*pi)*sin(37*pi/18) + cos(-2*pi)*cos(37*pi/18))*(-3*cos(4*pi/27) + 4*cos(4*pi/27)**3)/sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = -sin(37*pi/18) * sin(-2*pi) + cos(37*pi/18) * cos(-2*pi),
{
have : cos(pi/18) = cos((37*pi/18) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 18) * (4 * cos(4 * pi / 27) ** 3 - 3 * cos(4 * pi / 27)) / sin(pi / 9) = (-3*cos(4*pi/27) + 4*cos(4*pi/27)**3)*cos(pi/18)/sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = 4 * cos(4*pi/27) ** 3 - 3 * cos(4*pi/27),
{
have : cos(4*pi/9) = cos(3*(4*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18)*cos(4*pi/9) = cos(pi/2)/2 + cos(-7*pi/18)/2,
{
rw cos_mul_cos,
have : cos((pi/18) + (4*pi/9)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/18) - (4*pi/9)) = cos(-7*pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw cos_pi_div_two,
have : cos(-7*pi/18) = cos(7*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(7*pi/18) = sin(8*pi/9),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_295_GTAO_extend (h0 : sin(x)≠ 0) (h1 : (2*sin(x))≠ 0) (h2 : (2*cos(x+71*pi/2))≠ 0) : -sin(-2*x + 140*pi)/(2*cos(x + 71*pi/2)) + cos(x + 71*pi/2)=sqrt(2)*sin(x+pi/4):=
begin
have : -sin((-2) * x + 140 * pi) / (2 * cos(x + 71 * pi / 2)) + cos(x + 71 * pi / 2) = -sin(-2*x + 140*pi)/(2*cos(x + 71*pi/2)) + cos(x + 71*pi/2),
{
field_simp at *,
},
have : sin(2*x) = -sin(-2*x + 140*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (2*x) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 71 * pi / 2) + sin(2 * x) / (2 * cos(x + 71 * pi / 2)) = sin(2*x)/(2*cos(x + 71*pi/2)) + cos(x + 71*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = cos(x + 71*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(2*x) / ( 2 * sin(x) ),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/4) = sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(x+pi/4) = sin((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_four,
rw cos_pi_div_four,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_3_296_JKWR_extend : -1 + 2*(32*sin(6121*pi/72)**3*cos(pi/72)**3 - 6*sin(6121*pi/72)*cos(pi/72))**2=-sqrt(3)/2:=
begin
have : -1 + 2 * ((-32) * (-sin(6121 * pi / 72)) ** 3 * cos(pi / 72) ** 3 + 6 * -sin(6121 * pi / 72) * cos(pi / 72)) ** 2 = -1 + 2*(32*sin(6121*pi/72)**3*cos(pi/72)**3 - 6*sin(6121*pi/72)*cos(pi/72))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/72) = -sin(6121*pi/72),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (pi/72) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -1 + 2 * ((-4) * (2 * sin(pi / 72) * cos(pi / 72)) ** 3 + 3 * (2 * sin(pi / 72) * cos(pi / 72))) ** 2 = -1 + 2*(-32*sin(pi/72)**3*cos(pi/72)**3 + 6*sin(pi/72)*cos(pi/72))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) = 2 * sin(pi/72) * cos(pi/72),
{
have : sin(pi/36) = sin(2*(pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : 2 * ((-4) * sin(pi / 36) ** 3 + 3 * sin(pi / 36)) ** 2 - 1 = -1 + 2*(-4*sin(pi/36)**3 + 3*sin(pi/36))**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
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
rw sub_eq_neg_add,
have : -1 + 2*sin(pi/12)**2 = -cos(pi/6),
{
have : cos(pi/6) = 1 - 2*sin(pi/12)**2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
linarith,
},
rw this,
rw cos_pi_div_six,
ring_exp,
end


lemma Trigo_3_297_XHXV_extend(h0 : cos(13*pi/18) ≠ 0) (h1 : (-sin(31*pi/36)**2+(-sin(31*pi/72)**2+cos(31*pi/72)**2)**2)≠ 0) (h2 : (-1/2+cos(31*pi/18)/2+(-sin(31*pi/72)**2+cos(31*pi/72)**2)**2)≠ 0) (h3 : (-(1/2-cos(31*pi/18)/2)+(-sin(31*pi/72)**2+cos(31*pi/72)**2)**2)≠ 0) (h4 : ((-1)/2+cos(31*pi/18)/2+(-sin(31*pi/72)**2+(-sin(175*pi/72)*sin((-2)*pi)+cos(175*pi/72)*cos((-2)*pi))**2)**2)≠ 0) (h5 : (-1/2+cos(31*pi/18)/2+(-sin(31*pi/72)**2+(-sin(-2*pi)*sin(175*pi/72)+cos(-2*pi)*cos(175*pi/72))**2)**2)≠ 0) : sin(pi/9)*sin(11*pi/18)/(-1/2 + cos(31*pi/18)/2 + (-sin(31*pi/72)**2 + (-sin(-2*pi)*sin(175*pi/72) + cos(-2*pi)*cos(175*pi/72))**2)**2)=1/2:=
begin
have : sin(pi / 9) * sin(11 * pi / 18) / ((-1) / 2 + cos(31 * pi / 18) / 2 + (-sin(31 * pi / 72) ** 2 + (-sin(175 * pi / 72) * sin((-2) * pi) + cos(175 * pi / 72) * cos((-2) * pi)) ** 2) ** 2) = sin(pi/9)*sin(11*pi/18)/(-1/2 + cos(31*pi/18)/2 + (-sin(31*pi/72)**2 + (-sin(-2*pi)*sin(175*pi/72) + cos(-2*pi)*cos(175*pi/72))**2)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(31*pi/72) = -sin(175*pi/72) * sin(-2*pi) + cos(175*pi/72) * cos(-2*pi),
{
have : cos(31*pi/72) = cos((175*pi/72) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 9) * sin(11 * pi / 18) / (-(1 / 2 - cos(31 * pi / 18) / 2) + (-sin(31 * pi / 72) ** 2 + cos(31 * pi / 72) ** 2) ** 2) = sin(pi/9)*sin(11*pi/18)/(-1/2 + cos(31*pi/18)/2 + (-sin(31*pi/72)**2 + cos(31*pi/72)**2)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(31*pi/36) ** 2 = 1 / 2 - cos(31*pi/18) / 2,
{
have : cos(31*pi/18) = cos(2*(31*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(31*pi/36) = -sin(31*pi/72) ** 2 + cos(31*pi/72) ** 2,
{
have : cos(31*pi/36) = cos(2*(31*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9)*sin(11*pi/18) = (cos(pi/2)-cos(13*pi/18))/2,
{
rw mul_comm,
rw sin_mul_sin,
have : cos((11*pi/18) + (pi/9)) = cos(13*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos((11*pi/18) - (pi/9)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw cos_pi_div_two,
have : -sin(31*pi/36)**2 + cos(31*pi/36)**2 = cos(31*pi/18),
{
have : cos(31*pi/18) = cos(2*(31*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : cos(31*pi/18) = -cos(13*pi/18),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (31*pi/18) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_3_298_EJGL_extend : -cos(1198*pi/15)/2 - cos(-238*pi/3)/2 + (1 - 2*sin(7*pi/60)**2)*cos(pi/10)=1/2:=
begin
have : -(cos((-238) * pi / 3) / 2 + cos(1198 * pi / 15) / 2) + (1 - 2 * sin(7 * pi / 60) ** 2) * cos(pi / 10) = -cos(1198*pi/15)/2 - cos(-238*pi/3)/2 + (1 - 2*sin(7*pi/60)**2)*cos(pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/15) * cos(398*pi/5) = cos(-238*pi/3) / 2 + cos(1198*pi/15) / 2,
{
rw cos_mul_cos,
have : cos((4*pi/15) + (398*pi/5)) = cos(1198*pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : cos((4*pi/15) - (398*pi/5)) = cos(-238*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(cos(4*pi/15) * cos(398*pi/5)) = -cos(4*pi/15)*cos(398*pi/5),
{
ring,
},
conv {to_lhs, rw this,},
have : -cos(4 * pi / 15) * cos(398 * pi / 5) + cos(pi / 10) * (1 - 2 * sin(7 * pi / 60) ** 2) = -cos(4*pi/15)*cos(398*pi/5) + (1 - 2*sin(7*pi/60)**2)*cos(pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/30) = 1 - 2 * sin(7*pi/60) ** 2,
{
have : cos(7*pi/30) = cos(2*(7*pi/60)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : cos(pi / 10) * cos(7 * pi / 30) - cos(4 * pi / 15) * cos(398 * pi / 5) = -cos(4*pi/15)*cos(398*pi/5) + cos(pi/10)*cos(7*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/5) = cos(398*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/5) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/5) = sin(pi/10),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/5) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(4*pi/15) = sin(7*pi/30),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/15) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sub_eq_neg_add,
rw mul_comm,
rw ← neg_mul,
have : -sin(pi/10)*sin(7*pi/30) + cos(pi/10)*cos(7*pi/30) = cos(pi/3),
{
have : cos(pi/3) = cos((pi/10) + (7*pi/30)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_three,
end


lemma Trigo_3_299_ROBF_extend : (2*cos(x/2 - pi/8)**2 - 1)**2 - cos(x + 421*pi/4)**2=-cos(2*x + 297*pi/2):=
begin
have : sin(2*x) = -cos(2*x + 297*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*x) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : (2 * cos(x / 2 - pi / 8) ** 2 - 1) ** 2 - (-cos(x + 421 * pi / 4)) ** 2 = (2*cos(x/2 - pi/8)**2 - 1)**2 - cos(x + 421*pi/4)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-x + pi/4) = -cos(x + 421*pi/4),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + pi/4) (52),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(-x + pi / 4) ** 2 + (2 * cos(x / 2 - pi / 8) ** 2 - 1) ** 2 = (2*cos(x/2 - pi/8)**2 - 1)**2 - sin(-x + pi/4)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi/4) = 2 * cos(x/2 - pi/8) ** 2 - 1,
{
have : cos(x - pi/4) = cos(2*(x/2 - pi/8)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi/4)**2 = 1/2 + cos(2*x - pi/2)/2,
{
have : cos(2*x - pi/2) = cos(2*(x - pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
have : sin(-x + pi/4)**2 = 1/2 - cos(-2*x + pi/2)/2,
{
have : cos(-2*x + pi/2) = cos(2*(-x + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(-2*x + pi/2) = sin(2*x),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(2 * x - pi / 2) = sin(2*x),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*x-pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
ring,
end


lemma Trigo_4_300_HVNS_extend(h0 : sin(2*pi/9) ≥ 0) (h1 : sin(2*pi/9) ≠ 0)  (h2 : sqrt(1-cos(4*pi/9))≠ 0) : (sin(-pi)*sin(-17*pi/18) + sqrt(3)*sin(pi/18) + sin(191*pi/2)*cos(-17*pi/18))/sqrt(1 - cos(4*pi/9))=sqrt(2):=
begin
have : (sin(-pi) * sin((-17) * pi / 18) + sqrt 3 * sin(pi / 18) + cos((-17) * pi / 18) * sin(191 * pi / 2)) / sqrt (1 - cos(4 * pi / 9)) = (sin(-pi)*sin(-17*pi/18) + sqrt(3)*sin(pi/18) + sin(191*pi/2)*cos(-17*pi/18))/sqrt(1 - cos(4*pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(77*pi) = sin(191*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (77*pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi) * sin((-17) * pi / 18) + sqrt 3 * sin(pi / 18) + cos(77 * pi) * cos((-17) * pi / 18)) / sqrt (1 - cos(4 * pi / 9)) = (sin(-pi)*sin(-17*pi/18) + sqrt(3)*sin(pi/18) + cos(-17*pi/18)*cos(77*pi))/sqrt(1 - cos(4*pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) = cos(77*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-pi) (39),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * sin(pi / 18) + (sin((-17) * pi / 18) * sin(-pi) + cos((-17) * pi / 18) * cos(-pi))) / sqrt (1 - cos(4 * pi / 9)) = (sin(-pi)*sin(-17*pi/18) + sqrt(3)*sin(pi/18) + cos(-pi)*cos(-17*pi/18))/sqrt(1 - cos(4*pi/9)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = sin(-17*pi/18) * sin(-pi) + cos(-17*pi/18) * cos(-pi),
{
have : cos(pi/18) = cos((-17*pi/18) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
have : 1 - cos(4 * pi / 9) = sin(2*pi/9)**2 + cos(2*pi/9)**2 - cos(4*pi/9),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : cos(4*pi/9) = -sin(2*pi/9)**2 + cos(2*pi/9)**2,
{
have : cos(4*pi/9) = cos(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : sin(2*pi/9)**2 + cos(2*pi/9)**2 - (-sin(2*pi/9)**2 + cos(2*pi/9)**2) = 2*sin(2*pi/9)**2,
{
ring,
},
rw this,
rw sqrt_mul,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_4_301_SLSZ_extend : -sqrt(3)*cos(pi/12) + (-4*sin(7*pi/36)**3 + 3*sin(7*pi/36))*cos(pi/2) - (-3*cos(7*pi/36) + 4*cos(7*pi/36)**3)*sin(pi/2)=-sqrt(2):=
begin
have : -sqrt 3 * cos(pi / 12) + ((-4) * sin(7 * pi / 36) ** 3 + 3 * sin(7 * pi / 36)) * cos(pi / 2) - ((-3) * cos(7 * pi / 36) + 4 * cos(7 * pi / 36) ** 3) * sin(pi / 2) = -sqrt(3)*cos(pi/12) + (-4*sin(7*pi/36)**3 + 3*sin(7*pi/36))*cos(pi/2) - (-3*cos(7*pi/36) + 4*cos(7*pi/36)**3)*sin(pi/2),
{
field_simp at *,
},
have : sin(7*pi/12) = -4 * sin(7*pi/36) ** 3 + 3 * sin(7*pi/36),
{
have : sin(7*pi/12) = sin(3*(7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * cos(pi / 12) + sin(7 * pi / 12) * cos(pi / 2) - sin(pi / 2) * (4 * cos(7 * pi / 36) ** 3 - 3 * cos(7 * pi / 36)) = -sqrt(3)*cos(pi/12) + sin(7*pi/12)*cos(pi/2) - (-3*cos(7*pi/36) + 4*cos(7*pi/36)**3)*sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/12) = 4 * cos(7*pi/36) ** 3 - 3 * cos(7*pi/36),
{
have : cos(7*pi/12) = cos(3*(7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 12) * cos(pi / 2) - sin(pi / 2) * cos(7 * pi / 12) - sqrt 3 * cos(pi / 12) = -sqrt(3)*cos(pi/12) + sin(7*pi/12)*cos(pi/2) - sin(pi/2)*cos(7*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = sin(7*pi/12) * cos(pi/2) - sin(pi/2) * cos(7*pi/12),
{
have : sin(pi/12) = sin((7*pi/12) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3)*cos(pi/12) = 2*sin(pi/3)*cos(pi/12),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/12) = 2*sin(pi/12)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
rw sub_eq_neg_add,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/3)*cos(pi/12) + 2*sin(pi/12)*cos(pi/3) = 2*sin(-pi/4),
{
have : sin(-pi/4) = sin(pi/12)*cos(pi/3) - sin(pi/3)*cos(pi/12),
{
have : sin(-pi/4) = sin((pi/12) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : sin(-pi/4) = -sin(pi/4),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_302_SHAD_extend(h0 : cos(2*pi/9) ≠ 0) (h1 : 1 - tan(pi/9) * tan(2*pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0)  (h3 : cos(2*pi/9)≠ 0) (h4 : (cos(2*pi/9)*tan(583*pi/18))≠ 0) (h5 : tan(583*pi/18)≠ 0) (h6 : cos((583*pi/9)/2)≠ 0) (h7 : (1-cos(583*pi/9))≠ 0) (h8 : sin(583*pi/9)≠ 0) (h9 : (cos(2*pi/9)*((1-cos(583*pi/9))/sin(583*pi/9)))≠ 0) (h10 : ((1-cos(583*pi/9))/sin(583*pi/9))≠ 0) (h11 : ((1-cos(583*pi/9))*cos(2*pi/9))≠ 0) : sin(583*pi/9)/(1 - cos(583*pi/9)) + sqrt(3)*sin(2*pi/9)*sin(583*pi/9)/((1 - cos(583*pi/9))*cos(2*pi/9)) + sin(2*pi/9)/cos(2*pi/9)=sqrt(3):=
begin
have : 1 / ((1 - cos(583 * pi / 9)) / sin(583 * pi / 9)) + sqrt 3 * sin(2 * pi / 9) / (cos(2 * pi / 9) * ((1 - cos(583 * pi / 9)) / sin(583 * pi / 9))) + sin(2 * pi / 9) / cos(2 * pi / 9) = sin(583*pi/9)/(1 - cos(583*pi/9)) + sqrt(3)*sin(2*pi/9)*sin(583*pi/9)/((1 - cos(583*pi/9))*cos(2*pi/9)) + sin(2*pi/9)/cos(2*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(583*pi/18) = ( 1 - cos(583*pi/9) ) / sin(583*pi/9),
{
have : tan(583*pi/18) = tan((583*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : 1 / tan(583 * pi / 18) + sqrt 3 * sin(2 * pi / 9) * (1 / tan(583 * pi / 18)) / cos(2 * pi / 9) + sin(2 * pi / 9) / cos(2 * pi / 9) = 1/tan(583*pi/18) + sqrt(3)*sin(2*pi/9)/(cos(2*pi/9)*tan(583*pi/18)) + sin(2*pi/9)/cos(2*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = 1 / tan(583*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/9) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * tan(pi / 9) * (sin(2 * pi / 9) / cos(2 * pi / 9)) + tan(pi / 9) + sin(2 * pi / 9) / cos(2 * pi / 9) = tan(pi/9) + sqrt(3)*sin(2*pi/9)*tan(pi/9)/cos(2*pi/9) + sin(2*pi/9)/cos(2*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/9) = sin(2*pi/9) / cos(2*pi/9),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(pi/9) + tan(2*pi/9) = (-tan(pi/9)*tan(2*pi/9) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/9) + (2*pi/9)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
have : (-tan(pi/9)*tan(2*pi/9) + 1)*sqrt(3) = -sqrt(3)*tan(pi/9)*tan(2*pi/9) + sqrt(3),
{
ring_exp,
},
rw this,
norm_num,
end


lemma Trigo_4_303_WCHH_extend(h0 : 1 - tan(5*pi/36) * tan(7*pi/36) ≠ 0) (h1 : cos(5*pi/36) ≠ 0) (h2 : cos(7*pi/36) ≠ 0)  (h3 : cos(pi/36)≠ 0) (h4 : cos(-pi/6)≠ 0) (h5 : (tan(-pi/6)*tan(pi/36)+1)≠ 0) (h6 : (1+tan(pi/36)*tan(-pi/6))≠ 0) (h7 : (tan(-pi/6)*tan(1261*pi/36)+1)≠ 0) (h8 : cos(5*pi/36)≠ 0) (h9 : ((tan(-pi/6)*tan(1261*pi/36)+1)*cos(5*pi/36))≠ 0) : sin(5*pi/36)/cos(5*pi/36) + sqrt(3)*(tan(1261*pi/36) - tan(-pi/6))*sin(5*pi/36)/((tan(-pi/6)*tan(1261*pi/36) + 1)*cos(5*pi/36)) + (tan(1261*pi/36) - tan(-pi/6))/(tan(-pi/6)*tan(1261*pi/36) + 1)=sqrt(3):=
begin
have : sin(5 * pi / 36) / cos(5 * pi / 36) + sqrt 3 * (tan(1261 * pi / 36) - tan(-pi / 6)) * (sin(5 * pi / 36) / cos(5 * pi / 36)) / (tan(-pi / 6) * tan(1261 * pi / 36) + 1) + (tan(1261 * pi / 36) - tan(-pi / 6)) / (tan(-pi / 6) * tan(1261 * pi / 36) + 1) = sin(5*pi/36)/cos(5*pi/36) + sqrt(3)*(tan(1261*pi/36) - tan(-pi/6))*sin(5*pi/36)/((tan(-pi/6)*tan(1261*pi/36) + 1)*cos(5*pi/36)) + (tan(1261*pi/36) - tan(-pi/6))/(tan(-pi/6)*tan(1261*pi/36) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/36) = sin(5*pi/36) / cos(5*pi/36),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(5 * pi / 36) + sqrt 3 * (tan(1261 * pi / 36) - tan(-pi / 6)) * tan(5 * pi / 36) / (tan(-pi / 6) * tan(1261 * pi / 36) + 1) + (tan(1261 * pi / 36) - tan(-pi / 6)) / (tan(-pi / 6) * tan(1261 * pi / 36) + 1) = tan(5*pi/36) + sqrt(3)*(tan(1261*pi/36) - tan(-pi/6))*tan(5*pi/36)/(tan(-pi/6)*tan(1261*pi/36) + 1) + (tan(1261*pi/36) - tan(-pi/6))/(tan(-pi/6)*tan(1261*pi/36) + 1),
{
field_simp at *,
},
have : tan(pi/36) = tan(1261*pi/36),
{
rw tan_eq_tan_add_int_mul_pi (pi/36) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * tan(5 * pi / 36) * ((tan(pi / 36) - tan(-pi / 6)) / (1 + tan(pi / 36) * tan(-pi / 6))) + tan(5 * pi / 36) + (tan(pi / 36) - tan(-pi / 6)) / (1 + tan(pi / 36) * tan(-pi / 6)) = tan(5*pi/36) + sqrt(3)*(tan(pi/36) - tan(-pi/6))*tan(5*pi/36)/(tan(-pi/6)*tan(pi/36) + 1) + (tan(pi/36) - tan(-pi/6))/(tan(-pi/6)*tan(pi/36) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/36) = ( tan(pi/36) - tan(-pi/6) ) / ( 1 + tan(pi/36) * tan(-pi/6) ),
{
have : tan(7*pi/36) = tan((pi/36) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(5*pi/36) + tan(7*pi/36) = (-tan(5*pi/36)*tan(7*pi/36) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((5*pi/36) + (7*pi/36)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_three,
have : (-tan(5*pi/36)*tan(7*pi/36) + 1)*sqrt(3) = -sqrt(3)*tan(5*pi/36)*tan(7*pi/36) + sqrt(3),
{
ring_exp,
},
rw this,
norm_num,
end


lemma Trigo_4_304_VPTQ_extend(h0 : cos(pi/18) ≠ 0) (h1 : sin(4*pi/9) ≠ 0)  (h2 : cos(pi/9)≠ 0) (h3 : (4*cos(pi/9)**2)≠ 0) (h4 : (2*cos(pi/9))≠ 0) : (sqrt(3)*tan(541*pi/18) + 1)*(-sin(2*pi/9)**2/(4*cos(pi/9)**2) + 1/2)=1/2:=
begin
have : (1 / 2 - (sin(2 * pi / 9) / (2 * cos(pi / 9))) ** 2) * (sqrt 3 * tan(541 * pi / 18) + 1) = (sqrt(3)*tan(541*pi/18) + 1)*(-sin(2*pi/9)**2/(4*cos(pi/9)**2) + 1/2),
{
field_simp at *,
ring,
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
have : ((-1) / 2 + (1 - sin(pi / 9) ** 2)) * (sqrt 3 * tan(541 * pi / 18) + 1) = (1/2 - sin(pi/9)**2)*(sqrt(3)*tan(541*pi/18) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) ** 2 = 1 - sin(pi/9) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * tan(541 * pi / 18) + 1) * (cos(pi / 9) ** 2 - 1 / 2) = (-1/2 + cos(pi/9)**2)*(sqrt(3)*tan(541*pi/18) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = tan(541*pi/18),
{
rw tan_eq_tan_add_int_mul_pi (pi/18) (30),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9)**2 - 1/2 = cos(2*pi/9)/2,
{
have : cos(2*pi/9) = 2*cos(pi/9)**2 - 1,
{
have : cos(2*pi/9) = cos(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
have : sqrt(3)*(sin(pi/18)/cos(pi/18)) + 1 = (sqrt(3)*sin(pi/18) + cos(pi/18))/cos(pi/18),
{
field_simp,
},
rw this,
have : sqrt(3)*sin(pi/18) = 2*cos(pi/6)*sin(pi/18),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
rw mul_right_comm,
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
rw div_mul_eq_mul_div,
have : 2*sin(2*pi/9)*(cos(2*pi/9)/2)/(2*sin(pi/6)*cos(pi/18)) = sin(2*pi/9)*cos(2*pi/9)/(2*sin(pi/6)*cos(pi/18)),
{
ring,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(pi/18) = sin(4*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_305_XJWQ_extend : sin(347*pi/180)*cos(37*pi/45) + ((-sin(-2*pi)*sin(5*pi/2) + cos(-2*pi)*cos(5*pi/2))*sin(-13*pi/180) + sin(pi/2)*cos(-13*pi/180))*(-3*cos(29*pi/270) + 4*cos(29*pi/270)**3)=sqrt(2)/2:=
begin
have : sin(347 * pi / 180) * cos(37 * pi / 45) + (sin((-13) * pi / 180) * (-sin(5 * pi / 2) * sin((-2) * pi) + cos(5 * pi / 2) * cos((-2) * pi)) + sin(pi / 2) * cos((-13) * pi / 180)) * ((-3) * cos(29 * pi / 270) + 4 * cos(29 * pi / 270) ** 3) = sin(347*pi/180)*cos(37*pi/45) + ((-sin(-2*pi)*sin(5*pi/2) + cos(-2*pi)*cos(5*pi/2))*sin(-13*pi/180) + sin(pi/2)*cos(-13*pi/180))*(-3*cos(29*pi/270) + 4*cos(29*pi/270)**3),
{
field_simp at *,
repeat {left},
ring,
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
have : sin(347 * pi / 180) * cos(37 * pi / 45) + ((-3) * cos(29 * pi / 270) + 4 * cos(29 * pi / 270) ** 3) * (sin((-13) * pi / 180) * cos(pi / 2) + sin(pi / 2) * cos((-13) * pi / 180)) = sin(347*pi/180)*cos(37*pi/45) + (sin(-13*pi/180)*cos(pi/2) + sin(pi/2)*cos(-13*pi/180))*(-3*cos(29*pi/270) + 4*cos(29*pi/270)**3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(77*pi/180) = sin(-13*pi/180) * cos(pi/2) + sin(pi/2) * cos(-13*pi/180),
{
have : sin(77*pi/180) = sin((-13*pi/180) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(77 * pi / 180) * (4 * cos(29 * pi / 270) ** 3 - 3 * cos(29 * pi / 270)) + sin(347 * pi / 180) * cos(37 * pi / 45) = sin(347*pi/180)*cos(37*pi/45) + (-3*cos(29*pi/270) + 4*cos(29*pi/270)**3)*sin(77*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(29*pi/90) = 4 * cos(29*pi/270) ** 3 - 3 * cos(29*pi/270),
{
have : cos(29*pi/90) = cos(3*(29*pi/270)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(347*pi/180) = -cos(77*pi/180),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (347*pi/180) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(29*pi/90) = sin(8*pi/45),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (29*pi/90) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -cos(77*pi/180)*cos(37*pi/45) = -cos(71*pi/180)/2 - cos(5*pi/4)/2,
{
have : cos(77*pi/180)*cos(37*pi/45) = cos(71*pi/180)/2 + cos(5*pi/4)/2,
{
rw mul_comm,
rw cos_mul_cos,
have : cos((37*pi/45) + (77*pi/180)) = cos(5*pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos((37*pi/45) - (77*pi/180)) = cos(71*pi/180),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : sin(77*pi/180)*sin(8*pi/45) = -cos(109*pi/180)/2 + cos(pi/4)/2,
{
rw sin_mul_sin,
have : cos((77*pi/180) + (8*pi/45)) = cos(109*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : cos((77*pi/180) - (8*pi/45)) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(109*pi/180) = -cos(71*pi/180),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (109*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(5*pi/4) = -cos(pi/4),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_306_QRTB_extend : -sin(433*pi/4)**2 + (sin(pi/12)*cos(pi/6) + cos(pi/12)*cos(541*pi/3))**2 + sin(pi/2)=1:=
begin
have : cos(pi/4) = sin(433*pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(pi / 4) ** 2 + (sin(pi / 12) * cos(pi / 6) + cos(541 * pi / 3) * cos(pi / 12)) ** 2 + sin(pi / 2) = -cos(pi/4)**2 + (sin(pi/12)*cos(pi/6) + cos(pi/12)*cos(541*pi/3))**2 + sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = cos(541*pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (90),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 12) * cos(pi / 6) + sin(pi / 6) * cos(pi / 12)) ** 2 + sin(pi / 2) - cos(pi / 4) ** 2 = -cos(pi/4)**2 + (sin(pi/12)*cos(pi/6) + sin(pi/6)*cos(pi/12))**2 + sin(pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/4) = sin(pi/12) * cos(pi/6) + sin(pi/6) * cos(pi/12),
{
have : sin(pi/4) = sin((pi/12) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
rw ← sub_add_eq_add_sub,
have : sin(pi/4)**2 - cos(pi/4)**2 = -cos(pi/2),
{
have : cos(pi/2) = -sin(pi/4)**2 + cos(pi/4)**2,
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
linarith,
},
rw this,
rw cos_pi_div_two,
rw sin_pi_div_two,
norm_num,
end


lemma Trigo_4_307_ICEX_extend(h0 : sqrt(3) ≠ 0) (h1 : (cos((-7)*pi/6)**2*tan((-7)*pi/6))≠ 0) (h2 : (cos(-7*pi/6)**2*tan(-7*pi/6))≠ 0) (h3 : (sin(259*pi/3)**2*tan(-7*pi/6))≠ 0) (h4 : ((-sin(259*pi/3))**2*tan((-7)*pi/6))≠ 0) (h5 : sin(1949*pi/12)≠ 0) (h6 : (sin(259*pi/3)**2*tan((-7)*pi/6))≠ 0) (h7 : (4*sin(1949*pi/12)**4)≠ 0) (h8 : (2*sin(1949*pi/12))≠ 0) : (-1 + sin(1949*pi/6)**4/(4*sin(1949*pi/12)**4) - 2*cos(-17*pi/6))/(sin(259*pi/3)**2*tan(-7*pi/6))=-sqrt(3):=
begin
have : (-1 + 4 * (sin(1949 * pi / 6) / (2 * sin(1949 * pi / 12))) ** 4 - 2 * cos((-17) * pi / 6)) / (sin(259 * pi / 3) ** 2 * tan((-7) * pi / 6)) = (-1 + sin(1949*pi/6)**4/(4*sin(1949*pi/12)**4) - 2*cos(-17*pi/6))/(sin(259*pi/3)**2*tan(-7*pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1949*pi/12) = sin(1949*pi/6) / ( 2 * sin(1949*pi/12) ),
{
have : sin(1949*pi/6) = sin(2*(1949*pi/12)),
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
have : (-1 + 4 * cos(1949 * pi / 12) ** 4 - 2 * cos((-17) * pi / 6)) / ((-sin(259 * pi / 3)) ** 2 * tan((-7) * pi / 6)) = (-1 + 4*cos(1949*pi/12)**4 - 2*cos(-17*pi/6))/(sin(259*pi/3)**2*tan(-7*pi/6)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-7*pi/6) = -sin(259*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-7*pi/6) (43),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-2) * cos((-17) * pi / 6) + 4 * (-cos(1949 * pi / 12)) ** 4 - 1) / (cos((-7) * pi / 6) ** 2 * tan((-7) * pi / 6)) = (-1 + 4*cos(1949*pi/12)**4 - 2*cos(-17*pi/6))/(cos(-7*pi/6)**2*tan(-7*pi/6)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-17*pi/12) = -cos(1949*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-17*pi/12) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-17*pi/12) = -cos(5*pi/12),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-17*pi/12) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-17*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-17*pi/6) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-7*pi/6) = -cos(pi/6),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-7*pi/6) = -tan(pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-7*pi/6) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(5*pi/12) = sin(pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : (-sin(pi/12)) ** 4 = (sin(pi/12)**2)**2,
{
ring,
},
rw this,
have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
{
have : cos(pi/6) = cos(2*(pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
rw cos_pi_div_six,
rw tan_pi_div_six,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_4_308_RMHT_extend(h0 : cos(5*pi/12) ≠ 0)  (h1 : (1-tan(785*pi/12))≠ 0) (h2 : tan(37*pi/12)≠ 0) (h3 : (1-1/tan(37*pi/12))≠ 0) (h4 : (1-1/((-1)/tan(139*pi/12)))≠ 0) (h5 : tan(139*pi/12)≠ 0) (h6 : (tan(139*pi/12)+1)≠ 0) (h7 : ((-1)/tan(139*pi/12))≠ 0) : (1 - tan(139*pi/12))/(tan(139*pi/12) + 1)=-sqrt(3):=
begin
have : (1 + 1 / ((-1) / tan(139 * pi / 12))) / (1 - 1 / ((-1) / tan(139 * pi / 12))) = (1 - tan(139*pi/12))/(tan(139*pi/12) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(37*pi/12) = -1 / tan(139*pi/12),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (37*pi/12) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(785*pi/12) = 1 / tan(37*pi/12),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (785*pi/12) (68),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(785 * pi / 12) + 1) / (1 - tan(785 * pi / 12)) = (1 + tan(785*pi/12))/(1 - tan(785*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/12) = tan(785*pi/12),
{
rw tan_eq_tan_add_int_mul_pi (5*pi/12) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sin(5*pi/12)/cos(5*pi/12) + 1 = (cos(5*pi/12) + sin(5*pi/12))/cos(5*pi/12),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring,
},
rw this,
have : 1 - sin(5*pi/12)/cos(5*pi/12) = (-sin(5*pi/12) + cos(5*pi/12))/cos(5*pi/12),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring,
},
rw this,
have : sin(5*pi/12) = cos(pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(5*pi/12) + cos(pi/12) = 2*cos(pi/6)*cos(pi/4),
{
rw cos_add_cos,
have : cos(((5*pi/12) + (pi/12))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((5*pi/12) - (pi/12))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : -cos(pi/12) + cos(5*pi/12) = -2*sin(pi/6)*sin(pi/4),
{
rw neg_add_eq_sub,
rw cos_sub_cos,
have : sin(((5*pi/12) + (pi/12))/2) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((5*pi/12) - (pi/12))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw cos_pi_div_six,
rw cos_pi_div_four,
rw sin_pi_div_six,
rw sin_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_309_BJMY_extend(h0 : sin(pi/18)**2 + 1 ≠ 0)  (h1 : (2-(-sin(pi/36)**2+cos(pi/36)**2)**2)≠ 0) (h2 : (2-(-sin(pi/36)**2+(-sin((-11)*pi/36)*sin(pi/3)+cos((-11)*pi/36)*cos(pi/3))**2)**2)≠ 0) (h3 : (2-(-sin(pi/36)**2+(cos(-11*pi/36)*cos(pi/3)-sin(-11*pi/36)*sin(pi/3))**2)**2)≠ 0) (h4 : (2-(-1/2+cos(pi/18)/2+(cos(-11*pi/36)*cos(pi/3)-sin(-11*pi/36)*sin(pi/3))**2)**2)≠ 0) (h5 : (2-(-(1/2-cos(pi/18)/2)+(cos((-11)*pi/36)*cos(pi/3)-sin((-11)*pi/36)*sin(pi/3))**2)**2)≠ 0) : (3 - sin(7*pi/18))/(2 - (-1/2 + cos(pi/18)/2 + (cos(-11*pi/36)*cos(pi/3) - sin(-11*pi/36)*sin(pi/3))**2)**2)=2:=
begin
have : (3 - sin(7 * pi / 18)) / (2 - (-(1 / 2 - cos(pi / 18) / 2) + (cos((-11) * pi / 36) * cos(pi / 3) - sin((-11) * pi / 36) * sin(pi / 3)) ** 2) ** 2) = (3 - sin(7*pi/18))/(2 - (-1/2 + cos(pi/18)/2 + (cos(-11*pi/36)*cos(pi/3) - sin(-11*pi/36)*sin(pi/3))**2)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) ** 2 = 1 / 2 - cos(pi/18) / 2,
{
have : cos(pi/18) = cos(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
conv {to_lhs, rw ← this,},
have : (3 - sin(7 * pi / 18)) / (2 - (-sin(pi / 36) ** 2 + (-sin((-11) * pi / 36) * sin(pi / 3) + cos((-11) * pi / 36) * cos(pi / 3)) ** 2) ** 2) = (3 - sin(7*pi/18))/(2 - (-sin(pi/36)**2 + (cos(-11*pi/36)*cos(pi/3) - sin(-11*pi/36)*sin(pi/3))**2)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/36) = -sin(-11*pi/36) * sin(pi/3) + cos(-11*pi/36) * cos(pi/3),
{
have : cos(pi/36) = cos((-11*pi/36) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
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
have : sin(7*pi/18) = cos(pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/9) = -sin(pi/18)**2 + cos(pi/18)**2,
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
rw this,
rw cos_sq',
have : 2 - (1 - sin(pi/18)**2) = sin(pi/18)**2 + 1,
{
ring,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_4_310_KZFP_extend : -1 + (-sin(1391*pi/24)**2 + cos(23*pi/24)**2)**2=(sqrt(3)-2)/4:=
begin
have : -1 + (-(-sin(1391 * pi / 24)) ** 2 + cos(23 * pi / 24) ** 2) ** 2 = -1 + (-sin(1391*pi/24)**2 + cos(23*pi/24)**2)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(23*pi/24) = -sin(1391*pi/24),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (23*pi/24) (28),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(23*pi/12) = -sin(23*pi/24) ** 2 + cos(23*pi/24) ** 2,
{
have : cos(23*pi/12) = cos(2*(23*pi/24)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : cos(23 * pi / 12) ** 2 - 1 = -1 + cos(23*pi/12)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12) = cos(23*pi/12),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/12) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/12)**2 - 1 = sin(5*pi/12)**2 - (sin(5*pi/12)**2 + cos(5*pi/12)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : cos(5*pi/12) = -sin(pi/6)*sin(pi/4) + cos(pi/6)*cos(pi/4),
{
have : cos(5*pi/12) = cos((pi/4) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
rw sin_pi_div_six,
rw cos_pi_div_six,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring_exp,
rw sq_sqrt,
ring_exp,
repeat {linarith},
end


lemma Trigo_4_311_AZDL_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : ((-sin(2*x+pi/3)*sin(-pi/3)+cos(2*x+pi/3)*cos(-pi/3)+1)*cos(x+pi/2))≠ 0) (h3 : ((-sin(-pi/3)*sin(2*x+pi/3)+cos(-pi/3)*cos(2*x+pi/3)+1)*cos(x+pi/2))≠ 0) (h4 : ((sin(-pi/3)*cos(-2*x+163*pi/6)+cos(-pi/3)*cos(2*x+pi/3)+1)*cos(x+pi/2))≠ 0) (h5 : ((-sin(-pi/3)*-cos((-2)*x+163*pi/6)+cos(-pi/3)*cos(2*x+pi/3)+1)*cos(x+pi/2))≠ 0) (h6 : ((sin(-pi/3)*cos((-2)*x+163*pi/6)+cos(-pi/3)*cos(2*x+pi/3)+1)*cos(x+pi/2))≠ 0) : sin(-x + 249*pi/2)**2*sin(2*x + pi)/((sin(-pi/3)*cos(-2*x + 163*pi/6) + cos(-pi/3)*cos(2*x + pi/3) + 1)*cos(x + pi/2))=cos(x):=
begin
have : sin(2 * x + pi) * sin(-x + 249 * pi / 2) ** 2 / ((sin(-pi / 3) * cos((-2) * x + 163 * pi / 6) + cos(-pi / 3) * cos(2 * x + pi / 3) + 1) * cos(x + pi / 2)) = sin(-x + 249*pi/2)**2*sin(2*x + pi)/((sin(-pi/3)*cos(-2*x + 163*pi/6) + cos(-pi/3)*cos(2*x + pi/3) + 1)*cos(x + pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(-x + 249*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (x) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * x + pi) * cos(x) ** 2 / ((-sin(-pi / 3) * -cos((-2) * x + 163 * pi / 6) + cos(-pi / 3) * cos(2 * x + pi / 3) + 1) * cos(x + pi / 2)) = sin(2*x + pi)*cos(x)**2/((sin(-pi/3)*cos(-2*x + 163*pi/6) + cos(-pi/3)*cos(2*x + pi/3) + 1)*cos(x + pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*x + pi/3) = -cos(-2*x + 163*pi/6),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (2*x + pi/3) (13),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2 * x + pi) * cos(x) ** 2 / ((-sin(2 * x + pi / 3) * sin(-pi / 3) + cos(2 * x + pi / 3) * cos(-pi / 3) + 1) * cos(x + pi / 2)) = sin(2*x + pi)*cos(x)**2/((-sin(-pi/3)*sin(2*x + pi/3) + cos(-pi/3)*cos(2*x + pi/3) + 1)*cos(x + pi/2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -sin(2*x + pi/3) * sin(-pi/3) + cos(2*x + pi/3) * cos(-pi/3),
{
have : cos(2*x) = cos((2*x + pi/3) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x + pi) = -sin(2*x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
rw sin_sq,
have : -(1 - cos(x)**2) + cos(x)**2 + 1 = 2*cos(x)**2,
{
ring,
},
rw this,
have : cos(x + pi/2) = -sin(x),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_312_PTCV_extend : -sin(1129*pi/12)*sin(443*pi/3) + (sin(pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi))*sin(5*pi/12)=sqrt(2)/2:=
begin
have : sin(1129 * pi / 12) * -sin(443 * pi / 3) + (sin(pi) * cos((-5) * pi / 6) + sin((-5) * pi / 6) * cos(pi)) * sin(5 * pi / 12) = -sin(1129*pi/12)*sin(443*pi/3) + (sin(pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi))*sin(5*pi/12),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(443*pi/3),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 6) * sin(1129 * pi / 12) + (sin(pi) * cos((-5) * pi / 6) + sin((-5) * pi / 6) * cos(pi)) * sin(5 * pi / 12) = sin(1129*pi/12)*cos(pi/6) + (sin(pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi))*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(1129*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin((-5) * pi / 6) * cos(pi) + sin(pi) * cos((-5) * pi / 6)) * sin(5 * pi / 12) + cos(pi / 6) * cos(5 * pi / 12) = cos(pi/6)*cos(5*pi/12) + (sin(pi)*cos(-5*pi/6) + sin(-5*pi/6)*cos(pi))*sin(5*pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(-5*pi/6) * cos(pi) + sin(pi) * cos(-5*pi/6),
{
have : sin(pi/6) = sin((-5*pi/6) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
rw add_comm,
have : cos(pi/6)*cos(5*pi/12) + sin(pi/6)*sin(5*pi/12) = cos(-pi/4),
{
have : cos(-pi/4) = cos((pi/6) - (5*pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
},
rw this,
have : cos(-pi/4) = cos(pi/4),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_4_313_DPDC_extend (h0 : (-sin(pi/12)+-cos(589*pi/12))≠ 0) (h1 : (-sin(pi/12)-cos(589*pi/12))≠ 0) (h2 : (-sin(pi/12)-(sin(577*pi/12)*sin(-pi)+cos(577*pi/12)*cos(-pi)))≠ 0) (h3 : (-sin(pi/12)-sin(-pi)*sin(577*pi/12)-cos(-pi)*cos(577*pi/12))≠ 0) (h4 : (-sin(pi/12)-sin(-pi)*sin(577*pi/12)-(cos((-589)*pi/12)/2+cos(565*pi/12)/2))≠ 0) (h5 : (-sin(pi/12)-sin(-pi)*sin(577*pi/12)-cos(-589*pi/12)/2-cos(565*pi/12)/2)≠ 0) : (-sin(-pi)*sin(577*pi/12) + sin(pi/12) - cos(-589*pi/12)/2 - cos(565*pi/12)/2)/(-sin(pi/12) - sin(-pi)*sin(577*pi/12) - cos(-589*pi/12)/2 - cos(565*pi/12)/2)=sqrt(3):=
begin
have : (-sin(-pi) * sin(577 * pi / 12) + sin(pi / 12) - (cos((-589) * pi / 12) / 2 + cos(565 * pi / 12) / 2)) / (-sin(pi / 12) - sin(-pi) * sin(577 * pi / 12) - (cos((-589) * pi / 12) / 2 + cos(565 * pi / 12) / 2)) = (-sin(-pi)*sin(577*pi/12) + sin(pi/12) - cos(-589*pi/12)/2 - cos(565*pi/12)/2)/(-sin(pi/12) - sin(-pi)*sin(577*pi/12) - cos(-589*pi/12)/2 - cos(565*pi/12)/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi) * cos(577*pi/12) = cos(-589*pi/12) / 2 + cos(565*pi/12) / 2,
{
rw cos_mul_cos,
have : cos((-pi) + (577*pi/12)) = cos(565*pi/12),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-pi) - (577*pi/12)) = cos(-589*pi/12),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(-pi) * cos(577*pi/12)) = cos(-pi)*cos(577*pi/12),
{
ring,
},
have : (sin(pi / 12) - (sin(577 * pi / 12) * sin(-pi) + cos(577 * pi / 12) * cos(-pi))) / (-sin(pi / 12) - (sin(577 * pi / 12) * sin(-pi) + cos(577 * pi / 12) * cos(-pi))) = (-sin(-pi)*sin(577*pi/12) + sin(pi/12) - cos(-pi)*cos(577*pi/12))/(-sin(pi/12) - sin(-pi)*sin(577*pi/12) - cos(-pi)*cos(577*pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(589*pi/12) = sin(577*pi/12) * sin(-pi) + cos(577*pi/12) * cos(-pi),
{
have : cos(589*pi/12) = cos((577*pi/12) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 12) + -cos(589 * pi / 12)) / (-sin(pi / 12) + -cos(589 * pi / 12)) = (sin(pi/12) - cos(589*pi/12))/(-sin(pi/12) - cos(589*pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(589*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = cos(5*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(5*pi/12) + cos(pi/12) = 2*cos(pi/6)*cos(pi/4),
{
rw cos_add_cos,
have : cos(((5*pi/12) + (pi/12))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((5*pi/12) - (pi/12))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(pi/4) = sin(pi/4),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(5*pi/12) = sin(pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/12) = sin(5*pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw ← sub_eq_neg_add,
have : sin(5*pi/12) - sin(pi/12) = 2*sin(pi/6)*cos(pi/4),
{
rw sin_sub_sin,
have : cos(((5*pi/12) + (pi/12))/2) = cos(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((5*pi/12) - (pi/12))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sin_pi_div_four,
rw cos_pi_div_six,
rw sin_pi_div_six,
rw cos_pi_div_four,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_314_PHSV_extend : -cos(13*pi/90)*cos(17*pi/90) - sin(7457*pi/90)*cos(10741*pi/45)=-1/2:=
begin
have : sin(8747*pi/90) = cos(10741*pi/45),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (8747*pi/90) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/90) = sin(7457*pi/90),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (13*pi/90) (41),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 90) * -sin(8747 * pi / 90) - cos(13 * pi / 90) * cos(17 * pi / 90) = -cos(13*pi/90)*cos(17*pi/90) - sin(13*pi/90)*sin(8747*pi/90),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/90) = -sin(8747*pi/90),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (17*pi/90) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_eq_neg_add,
rw ← neg_mul,
have : -cos(13*pi/90)*cos(17*pi/90) + sin(13*pi/90)*sin(17*pi/90) = -cos(pi/3),
{
have : cos(pi/3) = -sin(13*pi/90)*sin(17*pi/90) + cos(13*pi/90)*cos(17*pi/90),
{
have : cos(pi/3) = cos((13*pi/90) + (17*pi/90)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
end


lemma Trigo_4_315_JZKD_extend(h0 : cos(5*pi/18) ≠ 0) (h1 : sin(2*pi/9) ≠ 0)  (h2 : cos((5*pi/9)/2)≠ 0) (h3 : (cos(5*pi/9)+1)≠ 0) (h4 : (1+cos(5*pi/9))≠ 0) : (-1 - sqrt(3)*cos(2825*pi/18)/(cos(5*pi/9) + 1))*cos(1270*pi/9)=-1:=
begin
have : (-1 + sqrt 3 * -cos(2825 * pi / 18) / (cos(5 * pi / 9) + 1)) * cos(1270 * pi / 9) = (-1 - sqrt(3)*cos(2825*pi/18)/(cos(5*pi/9) + 1))*cos(1270*pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/9) = -cos(2825*pi/18),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(-sqrt 3 * (sin(5 * pi / 9) / (1 + cos(5 * pi / 9))) + 1) * cos(1270 * pi / 9) = (-1 + sqrt(3)*sin(5*pi/9)/(cos(5*pi/9) + 1))*cos(1270*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/18) = sin(5*pi/9) / ( 1 + cos(5*pi/9) ),
{
have : tan(5*pi/18) = tan((5*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-sqrt 3 * tan(5 * pi / 18) + 1) * -cos(1270 * pi / 9) = -(-sqrt(3)*tan(5*pi/18) + 1)*cos(1270*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -cos(1270*pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/9) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : -sqrt(3)*(sin(5*pi/18)/cos(5*pi/18)) + 1 = (-sqrt(3)*sin(5*pi/18) + cos(5*pi/18))/cos(5*pi/18),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : -sqrt(3)*sin(5*pi/18) = -2*sin(5*pi/18)*sin(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : cos(5*pi/18) = 2*cos(5*pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : -2*sin(5*pi/18)*sin(pi/3) + 2*cos(5*pi/18)*cos(pi/3) = 2*cos(11*pi/18),
{
have : cos(11*pi/18) = -sin(5*pi/18)*sin(pi/3) + cos(5*pi/18)*cos(pi/3),
{
have : cos(11*pi/18) = cos((pi/3) + (5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
have : cos(11*pi/18) = -sin(pi/9),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (11*pi/18) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_assoc,
have : cos(5*pi/18)*cos(pi/3) = cos(5*pi/18)/2,
{
field_simp,
},
rw this,
have : cos(5*pi/18) = sin(2*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 2*-sin(pi/9)/(2*(sin(2*pi/9)/2))*cos(pi/9) = -2*sin(pi/9)*cos(pi/9)/(2*(sin(2*pi/9)/2)),
{
ring,
},
rw this,
have : -2*sin(pi/9)*cos(pi/9) = -sin(2*pi/9),
{
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_4_316_QHYQ_extend(h0 : 2 ≠ 0) (h1 : sin(x) + cos(x) ≠ 0)  (h2 : (2*sin(x/2)*cos(-x/2+64*pi)+2*cos(-x/2+64*pi)**2-1)≠ 0) (h3 : (2*(sin(x-64*pi)/2+sin(64*pi)/2)+2*cos(-x/2+64*pi)**2-1)≠ 0) (h4 : (sin(x-64*pi)+2*cos(-x/2+64*pi)**2-1+sin(64*pi))≠ 0) (h5 : (sin(x-64*pi)+2*cos(-x/2+64*pi)**2-1+(sin(66*pi)*cos((-2)*pi)+sin((-2)*pi)*cos(66*pi)))≠ 0) (h6 : (sin(x-64*pi)+2*cos(-x/2+64*pi)**2-1+sin(66*pi)*cos(-2*pi)+sin(-2*pi)*cos(66*pi))≠ 0) : sin(x + pi/4)/(sin(x - 64*pi) + 2*cos(-x/2 + 64*pi)**2 - 1 + sin(66*pi)*cos(-2*pi) + sin(-2*pi)*cos(66*pi))=sqrt(2)/2:=
begin
have : sin(x + pi / 4) / (sin(x - 64 * pi) + 2 * cos(-x / 2 + 64 * pi) ** 2 - 1 + (sin(66 * pi) * cos((-2) * pi) + sin((-2) * pi) * cos(66 * pi))) = sin(x + pi/4)/(sin(x - 64*pi) + 2*cos(-x/2 + 64*pi)**2 - 1 + sin(66*pi)*cos(-2*pi) + sin(-2*pi)*cos(66*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(64*pi) = sin(66*pi) * cos(-2*pi) + sin(-2*pi) * cos(66*pi),
{
have : sin(64*pi) = sin((66*pi) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi / 4) / (2 * (sin(x - 64 * pi) / 2 + sin(64 * pi) / 2) + 2 * cos(-x / 2 + 64 * pi) ** 2 - 1) = sin(x + pi/4)/(sin(x - 64*pi) + 2*cos(-x/2 + 64*pi)**2 - 1 + sin(64*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/2) * cos(-x/2 + 64*pi) = sin(x - 64*pi) / 2 + sin(64*pi) / 2,
{
rw sin_mul_cos,
have : sin((x/2) + (-x/2 + 64*pi)) = sin(64*pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((x/2) - (-x/2 + 64*pi)) = sin(x - 64*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : 2*(sin(x/2) * cos(-x/2 + 64*pi)) = 2*sin(x/2)*cos(-x/2+64*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(x/2) = cos(-x/2 + 64*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x/2) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/4) = sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(x+pi/4) = sin((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
have : 2*sin(x/2)*cos(x/2) = sin(x),
{
have : sin(x) = sin(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(x) + 2*cos(x/2)**2 - 1 = sin(x) + cos(x/2)**2 -sin(x/2)**2,
{
have : sin(x) + 2*cos(x/2)**2 - 1 = sin(x) + 2*cos(x/2)**2 - (sin(x/2)**2 + cos(x/2)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
ring,
},
rw this,
rw ← sub_add_eq_add_sub,
rw sub_eq_add_neg,
rw add_assoc,
have : -sin(x/2)**2 + cos(x/2)**2 = cos(x),
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_4_317_CRBD_extend(h0 : sin(3) - cos(3) ≥ 0)  : sqrt((-6*cos(-1 + 359*pi/6) + 8*cos(-1 + 359*pi/6)**3)*sin(-3 + 261*pi/2) + 1)=sin(3)-cos(3):=
begin
have : sqrt (-((-8) * cos(-1 + 359 * pi / 6) ** 3 + 6 * cos(-1 + 359 * pi / 6)) * sin(-3 + 261 * pi / 2) + 1) = sqrt((-6*cos(-1 + 359*pi/6) + 8*cos(-1 + 359*pi/6)**3)*sin(-3 + 261*pi/2) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-1 + pi/3) = cos(-1 + 359*pi/6),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (-1 + pi/3) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (2 * ((-4) * sin(-1 + pi / 3) ** 3 + 3 * sin(-1 + pi / 3)) * -sin(-3 + 261 * pi / 2) + 1) = sqrt(-(-8*sin(-1 + pi/3)**3 + 6*sin(-1 + pi/3))*sin(-3 + 261*pi/2) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-3 + pi) = -sin(-3 + 261*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-3 + pi) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (2 * ((-4) * sin(-1 + pi / 3) ** 3 + 3 * sin(-1 + pi / 3)) * cos(-3 + pi) + 1) = sqrt(2*(-4*sin(-1 + pi/3)**3 + 3*sin(-1 + pi/3))*cos(-3 + pi) + 1),
{
field_simp at *,
},
have : sin(-3 + pi) = -4 * sin(-1 + pi/3) ** 3 + 3 * sin(-1 + pi/3),
{
have : sin(-3 + pi) = sin(3*(-1 + pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-3 + pi) = sin(3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-3 + pi) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-3 + pi) = -cos(3),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3 + pi) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : 2*sin(3)*-cos(3) + 1 = -2*sin(3)*cos(3) + (sin(3)**2 + cos(3)**2),
{
rw sin_sq_add_cos_sq,
ring,
},
rw this,
have : -2*sin(3)*cos(3) + (sin(3)**2 + cos(3)**2) = (sin(3) - cos(3))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
end


lemma Trigo_4_318_OXCR_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : sin(-x-pi)≠ 0) (h3 : cos(-x + 3*pi/2)≠ 0) (h4 : cos(-x - pi)≠ 0) (h5 : tan((-x + 3*pi/2)+(-x - pi))≠ 0) (h6 : 1-tan(-x + 3*pi/2)*tan(-x - pi)≠ 0) (h7 : tan(-2*x+pi/2)≠ 0) (h8 : tan((-2)*x+pi/2)≠ 0) : -((-tan(-x - pi) - tan(-x + 3*pi/2))/tan(-2*x + pi/2) + 1)*sin(pi - x)*sin(x + 395*pi/2)/sin(-x - pi)=cos(-x + 73*pi):=
begin
have : -(-(tan(-x + 3 * pi / 2) + tan(-x - pi)) / tan((-2) * x + pi / 2) + 1) * sin(pi - x) * sin(x + 395 * pi / 2) / sin(-x - pi) = -((-tan(-x - pi) - tan(-x + 3*pi/2))/tan(-2*x + pi/2) + 1)*sin(pi - x)*sin(x + 395*pi/2)/sin(-x - pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-x + 3*pi/2) * tan(-x - pi) = -( tan(-x + 3*pi/2) + tan(-x - pi) ) / tan(-2*x + pi/2) + 1,
{
rw tan_mul_tan',
have : tan((-x + 3*pi/2) + (-x - pi)) = tan(-2*x + pi/2),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -(tan(-x + 3*pi/2) * tan(-x - pi))*sin(pi - x)*sin(x + 395*pi/2)/sin(-x - pi) = -sin(pi-x)*sin(x+395*pi/2)*tan(-x-pi)*tan(-x+3*pi/2)/sin(-x-pi),
{
ring,
},
conv {to_lhs, rw this,},
have : - -cos(-x + 73 * pi) = cos(-x + 73*pi),
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : cos(x) = -cos(-x + 73*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (x) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(pi - x) * -sin(x + 395 * pi / 2) * tan(-x - pi) * tan(-x + 3 * pi / 2) / sin(-x - pi) = -sin(pi - x)*sin(x + 395*pi/2)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = -sin(x + 395*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 2*pi) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x - pi) = -tan(x + pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(x + pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x + 3*pi/2) = 1/tan(x),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_319_WRXS_extend(h0 : cos(pi/18) ≠ 0)  (h1 : cos(-35*pi/18)≠ 0) (h2 : cos(-2*pi)≠ 0) (h3 : (1+tan((-35)*pi/18)*tan((-2)*pi))≠ 0) (h4 : (tan(-2*pi)*tan(-35*pi/18)+1)≠ 0) (h5 : cos(-35*pi/18)≠ 0) (h6 : cos(-2*pi)≠ 0) (h7 : (cos((-35)*pi/18)*cos((-2)*pi))≠ 0) (h8 : ((tan(-2*pi)*tan(-35*pi/18)+1)*cos(-2*pi)*cos(-35*pi/18))≠ 0) (h9 : (tan((-2)*pi)*tan((-35)*pi/18)+1)≠ 0) : (-sin(pi/18)/((tan(-2*pi)*tan(-35*pi/18) + 1)*cos(-2*pi)*cos(-35*pi/18)) + sqrt(3))*cos(1147*pi/18)=1:=
begin
have : ((-1) * (sin(pi / 18) / (cos((-35) * pi / 18) * cos((-2) * pi))) / (tan((-2) * pi) * tan((-35) * pi / 18) + 1) + sqrt 3) * cos(1147 * pi / 18) = (-sin(pi/18)/((tan(-2*pi)*tan(-35*pi/18) + 1)*cos(-2*pi)*cos(-35*pi/18)) + sqrt(3))*cos(1147*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-35*pi/18) - tan(-2*pi) = sin(pi/18) / ( cos(-35*pi/18) * cos(-2*pi) ),
{
rw tan_sub_tan',
have : sin((-35*pi/18) - (-2*pi)) = sin(pi/18),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -1*(tan(-35*pi/18) - tan(-2*pi))/(tan(-2*pi)*tan(-35*pi/18) + 1) + sqrt(3) = (-(-tan(-2*pi)+tan(-35*pi/18))/(tan(-2*pi)*tan(-35*pi/18)+1)+sqrt(3)),
{
ring,
},
conv {to_lhs, rw this,},
have : (-((tan((-35) * pi / 18) - tan((-2) * pi)) / (1 + tan((-35) * pi / 18) * tan((-2) * pi))) + sqrt 3) * cos(1147 * pi / 18) = (-(-tan(-2*pi) + tan(-35*pi/18))/(tan(-2*pi)*tan(-35*pi/18) + 1) + sqrt(3))*cos(1147*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = ( tan(-35*pi/18) - tan(-2*pi) ) / ( 1 + tan(-35*pi/18) * tan(-2*pi) ),
{
have : tan(pi/18) = tan((-35*pi/18) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-tan(pi / 18) + sqrt 3) * cos(1147 * pi / 18) = (-tan(pi/18) + sqrt(3))*cos(1147*pi/18),
{
field_simp at *,
},
have : cos(5*pi/18) = cos(1147*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/18) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : -(sin(pi/18)/cos(pi/18)) + sqrt(3) = (-sin(pi/18) + sqrt(3)*cos(pi/18))/cos(pi/18),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : sqrt(3)*cos(pi/18) = 2*sin(pi/3)*cos(pi/18),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/18) = 2*sin(pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/18)*cos(pi/3) + 2*sin(pi/3)*cos(pi/18) = 2*sin(5*pi/18),
{
have : sin(5*pi/18) = -sin(pi/18)*cos(pi/3) + sin(pi/3)*cos(pi/18),
{
have : sin(5*pi/18) = sin((pi/3) - (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
rw div_mul_eq_mul_div,
have : 2*sin(5*pi/18)*cos(5*pi/18) = sin(5*pi/9),
{
have : sin(5*pi/9) = sin(2*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(5*pi/9) = cos(pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
end


lemma Trigo_4_320_QBWT_extend (h0 : cos(-pi/10)≠ 0) (h1 : (2*cos(-pi/10))≠ 0) (h2 : (4*cos(-pi/10)**2)≠ 0) (h3 : (4*sin(337*pi/5)**2)≠ 0) (h4 : (4*(-sin(337*pi/5))**2)≠ 0) (h5 : (2*sin(337*pi/5))≠ 0) (h6 : (2*-sin(337*pi/5))≠ 0) : sin(-pi/5)**2/(4*sin(337*pi/5)**2) + (sin(-7*pi/15)/2 + sin(pi/15)/2)/(2*sin(337*pi/5)) + cos(4*pi/15)**2=3/4:=
begin
have : sin(-pi / 5) ** 2 / (4 * (-sin(337 * pi / 5)) ** 2) - (sin((-7) * pi / 15) / 2 + sin(pi / 15) / 2) / (2 * -sin(337 * pi / 5)) + cos(4 * pi / 15) ** 2 = sin(-pi/5)**2/(4*sin(337*pi/5)**2) + (sin(-7*pi/15)/2 + sin(pi/15)/2)/(2*sin(337*pi/5)) + cos(4*pi/15)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-pi/10) = -sin(337*pi/5),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (-pi/10) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi / 5) ** 2 / (4 * cos(-pi / 10) ** 2) - (sin((-7) * pi / 15) / 2 + sin(pi / 15) / 2) / (2 * cos(-pi / 10)) + cos(4 * pi / 15) ** 2 = sin(-pi/5)**2/(4*cos(-pi/10)**2) - (sin(-7*pi/15)/2 + sin(pi/15)/2)/(2*cos(-pi/10)) + cos(4*pi/15)**2,
{
field_simp at *,
},
have : sin(-pi/5) * cos(4*pi/15) = sin(-7*pi/15) / 2 + sin(pi/15) / 2,
{
rw sin_mul_cos,
have : sin((-pi/5) + (4*pi/15)) = sin(pi/15),
{
apply congr_arg,
ring,
},
rw this,
have : sin((-pi/5) - (4*pi/15)) = sin(-7*pi/15),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(-pi/5) * cos(4*pi/15))/(2*cos(-pi/10)) = sin(-pi/5)*cos(4*pi/15)/(2*cos(-pi/10)),
{
ring,
},
have : (sin(-pi / 5) / (2 * cos(-pi / 10))) ** 2 - sin(-pi / 5) / (2 * cos(-pi / 10)) * cos(4 * pi / 15) + cos(4 * pi / 15) ** 2 = sin(-pi/5)**2/(4*cos(-pi/10)**2) - sin(-pi/5)*cos(4*pi/15)/(2*cos(-pi/10)) + cos(4*pi/15)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/10) = sin(-pi/5) / ( 2 * cos(-pi/10) ),
{
have : sin(-pi/5) = sin(2*(-pi/10)),
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
have : sin(-pi/10)**2 = 1/2 - cos(-pi/5)/2,
{
have : cos(-pi/5) = cos(2*(-pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(4*pi/15)**2 = 1/2 + cos(8*pi/15)/2,
{
have : cos(8*pi/15) = cos(2*(4*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
have : cos(-pi/5) = cos(pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/5) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 1/2 - cos(pi/5)/2 - sin(-pi/10)*cos(4*pi/15) + (1/2 + cos(8*pi/15)/2) = cos(8*pi/15)/2 - cos(pi/5)/2 - sin(-pi/10)*cos(4*pi/15) + 1,
{
ring,
},
rw this,
have : cos(8*pi/15)/2 - cos(pi/5)/2 = -sin(11*pi/30)*sin(pi/6),
{
have : -cos(pi/5) + cos(8*pi/15) = -2*sin(pi/6)*sin(11*pi/30),
{
rw neg_add_eq_sub,
rw cos_sub_cos,
have : sin(((8*pi/15) + (pi/5))/2) = sin(11*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((8*pi/15) - (pi/5))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
have : sin(-pi/10)*cos(4*pi/15) = -sin(11*pi/30)/2 + sin(pi/6)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((4*pi/15) + (-pi/10)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((4*pi/15) - (-pi/10)) = sin(11*pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_321_RNEK_extend : (-cos(-2*pi)*cos(29*pi/12) + sin(-2*pi)*sin(29*pi/12))*sin(208*pi/3) + (-3*cos(pi/36) + 4*cos(pi/36)**3)*sin(pi/6)=sqrt(2)/2:=
begin
have : -(-sin((-2) * pi) * sin(29 * pi / 12) + cos((-2) * pi) * cos(29 * pi / 12)) * sin(208 * pi / 3) + sin(pi / 6) * (4 * cos(pi / 36) ** 3 - 3 * cos(pi / 36)) = (-cos(-2*pi)*cos(29*pi/12) + sin(-2*pi)*sin(29*pi/12))*sin(208*pi/3) + (-3*cos(pi/36) + 4*cos(pi/36)**3)*sin(pi/6),
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
have : -sin(208 * pi / 3) * (-sin(29 * pi / 12) * sin((-2) * pi) + cos(29 * pi / 12) * cos((-2) * pi)) + sin(pi / 6) * cos(pi / 12) = -(-sin(-2*pi)*sin(29*pi/12) + cos(-2*pi)*cos(29*pi/12))*sin(208*pi/3) + sin(pi/6)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = -sin(29*pi/12) * sin(-2*pi) + cos(29*pi/12) * cos(-2*pi),
{
have : cos(5*pi/12) = cos((29*pi/12) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 6) * cos(pi / 12) + -sin(208 * pi / 3) * cos(5 * pi / 12) = -sin(208*pi/3)*cos(5*pi/12) + sin(pi/6)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/6) = -sin(208*pi/3),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/6) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/12) = sin(pi/12),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_comm (cos(pi/6)) (sin(pi/12)),
have : sin(pi/12)*cos(pi/6) + sin(pi/6)*cos(pi/12) = sin(pi/4),
{
have : sin(pi/4) = sin((pi/6) + (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_four,
end


lemma Trigo_4_322_RFNH_extend : (1 - 2*sin(7*pi/72)**2)*sin(917*pi/18) + sin(4*pi/9)*cos(3539*pi/36)=sqrt(2)/2:=
begin
have : cos(11*pi/36) = cos(3539*pi/36),
{
rw cos_eq_cos_add_int_mul_two_pi (11*pi/36) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(917 * pi / 18) * (1 - 2 * sin(7 * pi / 72) ** 2) + sin(4 * pi / 9) * cos(11 * pi / 36) = (1 - 2*sin(7*pi/72)**2)*sin(917*pi/18) + sin(4*pi/9)*cos(11*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/36) = 1 - 2 * sin(7*pi/72) ** 2,
{
have : cos(7*pi/36) = cos(2*(7*pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 9) * cos(11 * pi / 36) + cos(7 * pi / 36) * sin(917 * pi / 18) = sin(917*pi/18)*cos(7*pi/36) + sin(4*pi/9)*cos(11*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = sin(917*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/36) = sin(7*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw add_comm,
rw mul_comm (sin(4*pi/9)) (sin(7*pi/36)),
have : cos(7*pi/36)*cos(4*pi/9) + sin(7*pi/36)*sin(4*pi/9) = cos(pi/4),
{
have : cos(pi/4) = cos((4*pi/9) - (7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw this,
rw cos_pi_div_four,
end


lemma Trigo_4_323_UTUG_extend(h0 : cos(4) - sin(4) ≥ 0) : sqrt(sin(553*pi/3)*cos(pi/3 + 8) - sin(pi/3 + 8)*cos(-pi/3) + 1)=sin(4 + 381*pi/2) - sin(4):=
begin
have : sqrt (- -sin(553 * pi / 3) * cos(pi / 3 + 8) - sin(pi / 3 + 8) * cos(-pi / 3) + 1) = sqrt(sin(553*pi/3)*cos(pi/3 + 8) - sin(pi/3 + 8)*cos(-pi/3) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-pi/3) = -sin(553*pi/3),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (1 - (sin(pi / 3 + 8) * cos(-pi / 3) + sin(-pi / 3) * cos(pi / 3 + 8))) = sqrt(-sin(-pi/3)*cos(pi/3 + 8) - sin(pi/3 + 8)*cos(-pi/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8) = sin(pi/3 + 8) * cos(-pi/3) + sin(-pi/3) * cos(pi/3 + 8),
{
have : sin(8) = sin((pi/3 + 8) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4) = sin(4 + 381*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (4) (95),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : 1 - sin(8) = cos(4)**2 + sin(4)**2 - sin(8),
{
rw cos_sq_add_sin_sq,
},
rw this,
have : sin(8) = 2*sin(4)*cos(4),
{
have : sin(8) = sin(2*(4)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : cos(4)**2 + sin(4)**2 - 2*sin(4)*cos(4) = (cos(4) - sin(4))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
end


lemma Trigo_4_324_UJQY_extend(h0 : cos(pi/18) ≠ 0) (h1 : sin(5*pi/18) ≠ 0)  (h2 : cos(1024*pi/9)≠ 0) (h3 : cos(1313*pi/36)≠ 0) (h4 : (1-tan(1313*pi/36)**2)≠ 0) : (-sqrt(3) - 2*tan(1313*pi/36)/(1 - tan(1313*pi/36)**2))*cos(pi/18)/cos(1024*pi/9)=-2:=
begin
have : (-sqrt 3 - 2 * tan(1313 * pi / 36) / (1 - tan(1313 * pi / 36) ** 2)) * cos(pi / 18) / cos(1024 * pi / 9) = (-sqrt(3) - 2*tan(1313*pi/36)/(1 - tan(1313*pi/36)**2))*cos(pi/18)/cos(1024*pi/9),
{
field_simp at *,
},
have : tan(1313*pi/18) = 2 * tan(1313*pi/36) / ( 1 - tan(1313*pi/36) ** 2 ),
{
have : tan(1313*pi/18) = tan(2*(1313*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-sqrt 3 + -tan(1313 * pi / 18)) * cos(pi / 18) / cos(1024 * pi / 9) = (-sqrt(3) - tan(1313*pi/18))*cos(pi/18)/cos(1024*pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = -tan(1313*pi/18),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/18) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 18) - sqrt 3) * cos(pi / 18) / cos(1024 * pi / 9) = (-sqrt(3) + tan(pi/18))*cos(pi/18)/cos(1024*pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = cos(1024*pi/9),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/18) (56),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sin(pi/18)/cos(pi/18) - sqrt(3) = (-sqrt(3)*cos(pi/18) + sin(pi/18))/cos(pi/18),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring,
},
rw this,
have : -sqrt(3)*cos(pi/18) = -2*cos(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/18) = 2*sin(pi/18)*sin(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : -2*cos(pi/18)*cos(pi/6) + 2*sin(pi/18)*sin(pi/6) = -2*cos(2*pi/9),
{
have : cos(2*pi/9) = -sin(pi/18)*sin(pi/6) + cos(pi/18)*cos(pi/6),
{
have : cos(2*pi/9) = cos((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
have : cos(2*pi/9) = -sin(-5*pi/18),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-5*pi/18) = -sin(5*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_325_DUZH_extend(h0 : cos(3*pi/20) ≠ 0) (h1 : cos(pi/60) ≠ 0) (h2 : 1 - tan(pi/60) * tan(3*pi/20) ≠ 0)  (h3 : cos(-19*pi/60)≠ 0) (h4 : cos(-pi/3)≠ 0) (h5 : (1+tan((-19)*pi/60)*tan(-pi/3))≠ 0) (h6 : (1+tan(-pi/3)*tan(-19*pi/60))≠ 0) (h7 : cos(-pi/3)≠ 0) (h8 : cos(-19*pi/60)≠ 0) (h9 : (cos(-pi/3)*cos((-19)*pi/60))≠ 0) (h10 : ((1+tan(-pi/3)*tan(-19*pi/60))*cos(-pi/3)*cos(-19*pi/60))≠ 0) (h11 : (1+tan(-pi/3)*tan((-19)*pi/60))≠ 0) (h12 : cos((2*pi/3)/2)≠ 0) (h13 : ((1+tan(-pi/3)*tan(-19*pi/60))*(cos(2*pi/3)+1)*cos(-pi/3)*cos(-19*pi/60))≠ 0) (h14 : (1+cos(2*pi/3))≠ 0) (h15 : (cos(2*pi/3)+1)≠ 0) (h16 : ((1+tan(-pi/3)*tan((-19)*pi/60))*cos(-pi/3)*cos((-19)*pi/60))≠ 0) : -sin(-pi/60)*tan(3*pi/20)/((1 + tan(-pi/3)*tan(-19*pi/60))*cos(-pi/3)*cos(-19*pi/60)) - sin(-pi/60)*sin(2*pi/3)/((1 + tan(-pi/3)*tan(-19*pi/60))*(cos(2*pi/3) + 1)*cos(-pi/3)*cos(-19*pi/60)) + sin(2*pi/3)*tan(3*pi/20)/(cos(2*pi/3) + 1)=1:=
begin
have : -sin(-pi / 60) * tan(3 * pi / 20) / ((1 + tan(-pi / 3) * tan((-19) * pi / 60)) * cos(-pi / 3) * cos((-19) * pi / 60)) - sin(-pi / 60) * (sin(2 * pi / 3) / (1 + cos(2 * pi / 3))) / ((1 + tan(-pi / 3) * tan((-19) * pi / 60)) * cos(-pi / 3) * cos((-19) * pi / 60)) + tan(3 * pi / 20) * (sin(2 * pi / 3) / (1 + cos(2 * pi / 3))) = -sin(-pi/60)*tan(3*pi/20)/((1 + tan(-pi/3)*tan(-19*pi/60))*cos(-pi/3)*cos(-19*pi/60)) - sin(-pi/60)*sin(2*pi/3)/((1 + tan(-pi/3)*tan(-19*pi/60))*(cos(2*pi/3) + 1)*cos(-pi/3)*cos(-19*pi/60)) + sin(2*pi/3)*tan(3*pi/20)/(cos(2*pi/3) + 1),
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
have : (-1) * (sin(-pi / 60) / (cos(-pi / 3) * cos((-19) * pi / 60))) * tan(3 * pi / 20) / (1 + tan(-pi / 3) * tan((-19) * pi / 60)) + (-1) * (sin(-pi / 60) / (cos(-pi / 3) * cos((-19) * pi / 60))) * tan(pi / 3) / (1 + tan(-pi / 3) * tan((-19) * pi / 60)) + tan(3 * pi / 20) * tan(pi / 3) = -sin(-pi/60)*tan(3*pi/20)/((1 + tan(-pi/3)*tan(-19*pi/60))*cos(-pi/3)*cos(-19*pi/60)) - sin(-pi/60)*tan(pi/3)/((1 + tan(-pi/3)*tan(-19*pi/60))*cos(-pi/3)*cos(-19*pi/60)) + tan(3*pi/20)*tan(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-pi/3) - tan(-19*pi/60) = sin(-pi/60) / ( cos(-pi/3) * cos(-19*pi/60) ),
{
rw tan_sub_tan',
have : sin((-pi/3) - (-19*pi/60)) = sin(-pi/60),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -1*(tan(-pi/3) - tan(-19*pi/60)) = (tan(-19*pi/60)-tan(-pi/3)),
{
ring,
},
conv {to_lhs, rw this,},
have : (tan((-19) * pi / 60) - tan(-pi / 3)) / (1 + tan((-19) * pi / 60) * tan(-pi / 3)) * tan(3 * pi / 20) + (tan((-19) * pi / 60) - tan(-pi / 3)) / (1 + tan((-19) * pi / 60) * tan(-pi / 3)) * tan(pi / 3) + tan(3 * pi / 20) * tan(pi / 3) = (tan(-19*pi/60) - tan(-pi/3))*tan(3*pi/20)/(1 + tan(-pi/3)*tan(-19*pi/60)) + (tan(-19*pi/60) - tan(-pi/3))*tan(pi/3)/(1 + tan(-pi/3)*tan(-19*pi/60)) + tan(3*pi/20)*tan(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/60) = ( tan(-19*pi/60) - tan(-pi/3) ) / ( 1 + tan(-19*pi/60) * tan(-pi/3) ),
{
have : tan(pi/60) = tan((-19*pi/60) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(pi/60)*tan(pi/3) + tan(3*pi/20)*tan(pi/3) = (tan(pi/60) + tan(3*pi/20))*tan(pi/3),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three, -sin_pi_div_two, -cos_pi_div_two],
ring_exp,
},
rw this,
have : tan(pi/60) + tan(3*pi/20) = (-tan(pi/60)*tan(3*pi/20) + 1)*tan(pi/6),
{
rw tan_add_tan,
have : tan((pi/60) + (3*pi/20)) = tan(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/60)*tan(3*pi/20) + 1)*tan(pi/6) = -tan(pi/60)*tan(3*pi/20)*tan(pi/6) + tan(pi/6),
{
ring_exp,
},
rw this,
have : (-tan(pi/60)*tan(3*pi/20)*tan(pi/6) + tan(pi/6))*tan(pi/3) = -tan(pi/60)*tan(3*pi/20)*tan(pi/6)*tan(pi/3) + tan(pi/6)*tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_six,
rw tan_pi_div_three,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_4_326_TRVW_extend(h0 : 3 - sin(pi/18) ≠ 0)  (h1 : ((sin(5*pi/9)*cos(-pi/3)+sin(-pi/3)*cos(5*pi/9))**2+1)≠ 0) (h2 : ((sin(-pi/3)*cos(5*pi/9)+sin(5*pi/9)*cos(-pi/3))**2+1)≠ 0) (h3 : (((-3*cos(5*pi/27)+4*cos(5*pi/27)**3)*sin(-pi/3)+sin(5*pi/9)*cos(-pi/3))**2+1)≠ 0) (h4 : ((sin(-pi/3)*(4*cos(5*pi/27)**3-3*cos(5*pi/27))+sin(5*pi/9)*cos(-pi/3))**2+1)≠ 0) (h5 : (((-3*cos(5*pi/27)+4*cos(5*pi/27)**3)*sin(-pi/3)+sin(8*pi/9)/2+sin(2*pi/9)/2)**2+1)≠ 0) (h6 : ((((-3)*cos(5*pi/27)+4*cos(5*pi/27)**3)*sin(-pi/3)+(sin(8*pi/9)/2+sin(2*pi/9)/2))**2+1)≠ 0) : (3 - sin(17*pi/18))/(((-3*cos(5*pi/27) + 4*cos(5*pi/27)**3)*sin(-pi/3) + sin(8*pi/9)/2 + sin(2*pi/9)/2)**2 + 1)=2:=
begin
have : (3 - sin(17 * pi / 18)) / ((((-3) * cos(5 * pi / 27) + 4 * cos(5 * pi / 27) ** 3) * sin(-pi / 3) + (sin(8 * pi / 9) / 2 + sin(2 * pi / 9) / 2)) ** 2 + 1) = (3 - sin(17*pi/18))/(((-3*cos(5*pi/27) + 4*cos(5*pi/27)**3)*sin(-pi/3) + sin(8*pi/9)/2 + sin(2*pi/9)/2)**2 + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/9) * cos(-pi/3) = sin(8*pi/9) / 2 + sin(2*pi/9) / 2,
{
rw sin_mul_cos,
have : sin((5*pi/9) + (-pi/3)) = sin(2*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((5*pi/9) - (-pi/3)) = sin(8*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(5*pi/9) * cos(-pi/3)) = sin(5*pi/9)*cos(-pi/3),
{
ring,
},
have : (3 - sin(17 * pi / 18)) / ((sin(-pi / 3) * (4 * cos(5 * pi / 27) ** 3 - 3 * cos(5 * pi / 27)) + sin(5 * pi / 9) * cos(-pi / 3)) ** 2 + 1) = (3 - sin(17*pi/18))/(((-3*cos(5*pi/27) + 4*cos(5*pi/27)**3)*sin(-pi/3) + sin(5*pi/9)*cos(-pi/3))**2 + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/9) = 4 * cos(5*pi/27) ** 3 - 3 * cos(5*pi/27),
{
have : cos(5*pi/9) = cos(3*(5*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : (3 - sin(17 * pi / 18)) / ((sin(5 * pi / 9) * cos(-pi / 3) + sin(-pi / 3) * cos(5 * pi / 9)) ** 2 + 1) = (3 - sin(17*pi/18))/((sin(-pi/3)*cos(5*pi/9) + sin(5*pi/9)*cos(-pi/3))**2 + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = sin(5*pi/9) * cos(-pi/3) + sin(-pi/3) * cos(5*pi/9),
{
have : sin(2*pi/9) = sin((5*pi/9) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(17*pi/18) = sin(pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(2*pi/9)**2 = 1/2 - cos(4*pi/9)/2,
{
have : cos(4*pi/9) = cos(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(4*pi/9) = sin(pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 1/2 - sin(pi/18)/2 + 1 = (3 - sin(pi/18))/2,
{
ring,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_4_327_DOGX_extend(h0 : cos(pi/9) ≥ 0) (h1 : -cos(pi/9) + sin(pi/9) ≤ 0)  : sqrt(-2*sin(10*pi/9)*sin(29*pi/18) + 1) + sqrt(1 - cos(493*pi/18)**2)=2*cos(pi/9)-sin(pi/9):=
begin
have : sqrt ((-2) * sin(10 * pi / 9) * sin(29 * pi / 18) + 1) + sqrt (1 - (-cos(493 * pi / 18)) ** 2) = sqrt(-2*sin(10*pi/9)*sin(29*pi/18) + 1) + sqrt(1 - cos(493*pi/18)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(3053*pi/18) = -cos(493*pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3053*pi/18) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(10 * pi / 9) * sin(29 * pi / 18) + 1) + sqrt (1 - cos(3053 * pi / 18) ** 2) = sqrt(-2*sin(10*pi/9)*sin(29*pi/18) + 1) + sqrt(1 - cos(3053*pi/18)**2),
{
field_simp at *,
},
have : sin(8*pi/9) = cos(3053*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (8*pi/9) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt (1 - sin(8 * pi / 9) ** 2) + sqrt ((-2) * sin(10 * pi / 9) * sin(29 * pi / 18) + 1) = sqrt(-2*sin(10*pi/9)*sin(29*pi/18) + 1) + sqrt(1 - sin(8*pi/9)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(10*pi/9) = sin(29*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (10*pi/9) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(10*pi/9) = -sin(pi/9),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (10*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(10*pi/9) = -cos(pi/9),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (10*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw ← cos_sq',
have : -2*-sin(pi/9)*-cos(pi/9) + 1 = -2*sin(pi/9)*cos(pi/9) + (sin(pi/9)**2 + cos(pi/9)**2),
{
rw sin_sq_add_cos_sq,
ring,
},
rw this,
have : -2*sin(pi/9)*cos(pi/9) + (sin(pi/9)**2 + cos(pi/9)**2) = (-cos(pi/9) + sin(pi/9))**2,
{
ring_exp,
},
rw this,
repeat {rw sqrt_sq_eq_abs},
rw abs_eq_self.mpr h0,
rw abs_eq_neg_self.mpr h1,
norm_num,
ring_exp,
end


lemma Trigo_4_328_IZYH_extend(h0 : 1 - tan(pi/18) * tan(5*pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : cos(5*pi/18) ≠ 0) (h3 : tan(pi/18) ≠ 0) (h4 : tan(5*pi/18) ≠ 0)  (h5 : cos(-17*pi/18)≠ 0) (h6 : cos(-pi)≠ 0) (h7 : ((-tan(-pi)+tan(-17*pi/18))*tan(5*pi/18))≠ 0) (h8 : (1+tan((-17)*pi/18)*tan(-pi))≠ 0) (h9 : ((tan((-17)*pi/18)-tan(-pi))/(1+tan((-17)*pi/18)*tan(-pi))*tan(5*pi/18))≠ 0) (h10 : (tan(-pi)*tan(-17*pi/18)+1)≠ 0) (h11 : cos(-17*pi/18)≠ 0) (h12 : cos(-pi)≠ 0) (h13 : tan((-17*pi/18)-(-pi))≠ 0) (h14 : 1+tan(-17*pi/18)*tan(-pi)≠ 0) (h15 : ((-tan(-pi)+tan((-17)*pi/18))*tan(5*pi/18))≠ 0) (h16 : ((tan((-17)*pi/18)-tan(-pi))/tan(pi/18)-1+1)≠ 0) (h17 : (tan(pi/18)*tan(5*pi/18))≠ 0) (h18 : tan(pi/18)≠ 0) (h19 : cos((4*pi/3)/2)≠ 0) (h20 : (cos(4*pi/3)+1)≠ 0) (h21 : (1+cos(4*pi/3))≠ 0) : (sin(4*pi/3)/(cos(4*pi/3) + 1) + tan(pi/18) + tan(5*pi/18))/(tan(pi/18)*tan(5*pi/18))=-sqrt(3):=
begin
have : (sin(4 * pi / 3) / (1 + cos(4 * pi / 3)) + tan(pi / 18) + tan(5 * pi / 18)) / (tan(pi / 18) * tan(5 * pi / 18)) = (sin(4*pi/3)/(cos(4*pi/3) + 1) + tan(pi/18) + tan(5*pi/18))/(tan(pi/18)*tan(5*pi/18)),
{
field_simp at *,
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
have : ((tan((-17) * pi / 18) - tan(-pi)) / tan(pi / 18) - 1 + 1) * (tan(2 * pi / 3) + (-tan(-pi) + tan((-17) * pi / 18)) / ((tan((-17) * pi / 18) - tan(-pi)) / tan(pi / 18) - 1 + 1) + tan(5 * pi / 18)) / ((-tan(-pi) + tan((-17) * pi / 18)) * tan(5 * pi / 18)) = (tan(2*pi/3) + tan(pi/18) + tan(5*pi/18))/(tan(pi/18)*tan(5*pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-17*pi/18) * tan(-pi) = ( tan(-17*pi/18) - tan(-pi) ) / tan(pi/18) - 1,
{
rw tan_mul_tan,
have : tan((-17*pi/18) - (-pi)) = tan(pi/18),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(-17*pi/18) * tan(-pi)) = tan(-pi)*tan(-17*pi/18),
{
ring,
},
conv {to_lhs, rw this,},
have : ((tan((-17) * pi / 18) - tan(-pi)) / (1 + tan((-17) * pi / 18) * tan(-pi)) + tan(5 * pi / 18) + tan(2 * pi / 3)) / ((tan((-17) * pi / 18) - tan(-pi)) / (1 + tan((-17) * pi / 18) * tan(-pi)) * tan(5 * pi / 18)) = (tan(-pi)*tan(-17*pi/18) + 1)*(tan(2*pi/3) + (-tan(-pi) + tan(-17*pi/18))/(tan(-pi)*tan(-17*pi/18) + 1) + tan(5*pi/18))/((-tan(-pi) + tan(-17*pi/18))*tan(5*pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = ( tan(-17*pi/18) - tan(-pi) ) / ( 1 + tan(-17*pi/18) * tan(-pi) ),
{
have : tan(pi/18) = tan((-17*pi/18) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(pi/18) + tan(5*pi/18) = (-tan(pi/18)*tan(5*pi/18) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/18) + (5*pi/18)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/18)*tan(5*pi/18) + 1)*tan(pi/3) = -tan(pi/18)*tan(5*pi/18)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_329_APFG_extend : sin(-969*pi/10)*sin(5897*pi/30) + sin(-969*pi/10)**2 + sin(5897*pi/30)**2=3/4:=
begin
have : - -sin((-969) * pi / 10) * sin(5897 * pi / 30) + (-sin((-969) * pi / 10)) ** 2 + sin(5897 * pi / 30) ** 2 = sin(-969*pi/10)*sin(5897*pi/30) + sin(-969*pi/10)**2 + sin(5897*pi/30)**2,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(1009*pi/10) = -sin(-969*pi/10),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (1009*pi/10) (2),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/10) = sin(1009*pi/10),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/10) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 10) ** 2 - sin(pi / 10) * sin(5897 * pi / 30) + sin(5897 * pi / 30) ** 2 = -sin(pi/10)*sin(5897*pi/30) + sin(pi/10)**2 + sin(5897*pi/30)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/15) = sin(5897*pi/30),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/15) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/10)*cos(pi/15) = sin(pi/6)/2 + sin(pi/30)/2,
{
rw sin_mul_cos,
have : sin((pi/10) + (pi/15)) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/10) - (pi/15)) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(pi/10)**2 = 1/2 - cos(pi/5)/2,
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(pi/15)**2 = 1/2 + cos(2*pi/15)/2,
{
have : cos(2*pi/15) = cos(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
have : 1/2 - cos(pi/5)/2 - (sin(pi/6)/2 + sin(pi/30)/2) + (1/2 + cos(2*pi/15)/2) = -cos(pi/5)/2 + cos(2*pi/15)/2 - (sin(pi/6)/2 + sin(pi/30)/2) + 1,
{
ring,
},
rw this,
have : -cos(pi/5)/2 + cos(2*pi/15)/2 = sin(pi/30)*sin(pi/6),
{
have : -cos(2*pi/15) + cos(pi/5) = -2*sin(pi/30)*sin(pi/6),
{
rw neg_add_eq_sub,
rw cos_sub_cos,
have : sin(((pi/5) + (2*pi/15))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((pi/5) - (2*pi/15))/2) = sin(pi/30),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_330_QHIH_extend(h0 : sin(pi/9) ≠ 0)  : -(-4*sin(1231*pi/54)**3 + 3*sin(1231*pi/54))*sin(5*pi/18)*cos(1669*pi/9)=1/8:=
begin
have : -sin(5 * pi / 18) * ((-4) * sin(1231 * pi / 54) ** 3 + 3 * sin(1231 * pi / 54)) * cos(1669 * pi / 9) = -(-4*sin(1231*pi/54)**3 + 3*sin(1231*pi/54))*sin(5*pi/18)*cos(1669*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1231*pi/18) = -4 * sin(1231*pi/54) ** 3 + 3 * sin(1231*pi/54),
{
have : sin(1231*pi/18) = sin(3*(1231*pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos(1669 * pi / 9) * sin(5 * pi / 18) * sin(1231 * pi / 18) = -sin(5*pi/18)*sin(1231*pi/18)*cos(1669*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = -cos(1669*pi/9),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/18) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = sin(1231*pi/18),
{
rw sin_eq_sin_add_int_mul_two_pi (7*pi/18) (34),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = cos(4*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/18) = cos(2*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/18) = cos(pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : cos(4*pi/9)*cos(2*pi/9)*(sin(2*pi/9)/(2*sin(pi/9))) = sin(2*pi/9)*cos(2*pi/9)*cos(4*pi/9)/(2*sin(pi/9)),
{
ring,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/9)/2*cos(4*pi/9)/(2*sin(pi/9)) = sin(4*pi/9)*cos(4*pi/9)/2/(2*sin(pi/9)),
{
ring_exp,
},
rw this,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_4_331_NSKW_extend(h0 : 2 ≠ 0) (h1 : 2*sin(x)*cos(x) + 2*cos(x)**2 ≠ 0) (h2 : cos(x) ≠ 0)  (h3 : (sin(2*x)+2*(1-sin(x)**2))≠ 0) (h4 : (-2*sin(x)**2+sin(2*x)+2)≠ 0) (h5 : cos(x)≠ 0) (h6 : (-sin(2*x)**2/(2*cos(x)**2)+sin(2*x)+2)≠ 0) (h7 : ((-2)*(sin(2*x)/(2*cos(x)))**2+sin(2*x)+2)≠ 0) (h8 : (2*cos(x))≠ 0) (h9 : (2*cos(x)**2)≠ 0) (h10 : (2*(4*cos(x/3)**3-3*cos(x/3))**2)≠ 0) (h11 : (-sin(2*x)**2/(2*(4*cos(x/3)**3-3*cos(x/3))**2)+sin(2*x)+2)≠ 0) (h12 : (sin(2*x)+2-sin(2*x)**2/(2*(4*cos(x/3)**3-3*cos(x/3))**2))≠ 0) : (sin(2*x) + 1)/(sin(2*x) + 2 - sin(2*x)**2/(2*(4*cos(x/3)**3 - 3*cos(x/3))**2))=1/2*tan(x)+1/2:=
begin
have : (sin(2 * x) + 1) / (-sin(2 * x) ** 2 / (2 * (4 * cos(x / 3) ** 3 - 3 * cos(x / 3)) ** 2) + sin(2 * x) + 2) = (sin(2*x) + 1)/(sin(2*x) + 2 - sin(2*x)**2/(2*(4*cos(x/3)**3 - 3*cos(x/3))**2)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = 4 * cos(x/3) ** 3 - 3 * cos(x/3),
{
have : cos(x) = cos(3*(x/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * x) + 1) / ((-2) * (sin(2 * x) / (2 * cos(x))) ** 2 + sin(2 * x) + 2) = (sin(2*x) + 1)/(-sin(2*x)**2/(2*cos(x)**2) + sin(2*x) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = sin(2*x) / ( 2 * cos(x) ),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * x) + 1) / (sin(2 * x) + 2 * (1 - sin(x) ** 2)) = (sin(2*x) + 1)/(-2*sin(x)**2 + sin(2*x) + 2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) ** 2 = 1 - sin(x) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
have : 2*sin(x)*cos(x) + 1 = 2*sin(x)*cos(x) + (sin(x)**2 + cos(x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : 2*sin(x)*cos(x) + (sin(x)**2 + cos(x)**2) = (sin(x) + cos(x))**2,
{
ring_exp,
},
rw this,
have : (sin(x) + cos(x))**2/(2*sin(x)*cos(x) + 2*cos(x)**2) = (sin(x) + cos(x))/(2*cos(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring_exp,
end


lemma Trigo_4_332_DYHV_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (sin(x-pi)*cos(x+pi/2))≠ 0) (h3 : (sin(x-pi)*cos(-x-pi)*cos(x+pi/2))≠ 0) (h4 : cos(-x-pi)≠ 0) : -sin(pi - x)*sin(-x + 20*pi)*sin(x + 387*pi/2)*cos(-x + 2*pi)/(sin(x - pi)*cos(-x - pi)*cos(x + pi/2))=cos(x):=
begin
have : sin(pi - x) * -sin(-x + 20 * pi) * sin(x + 387 * pi / 2) * cos(-x + 2 * pi) / (sin(x - pi) * cos(-x - pi) * cos(x + pi / 2)) = -sin(pi - x)*sin(-x + 20*pi)*sin(x + 387*pi/2)*cos(-x + 2*pi)/(sin(x - pi)*cos(-x - pi)*cos(x + pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-x - pi) = -sin(-x + 20*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-x - pi) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + 3*pi/2) = sin(x + 387*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (x + 3*pi/2) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) * sin(x + 3 * pi / 2) * cos(-x + 2 * pi) * (sin(-x - pi) / cos(-x - pi)) / (sin(x - pi) * cos(x + pi / 2)) = sin(pi - x)*sin(-x - pi)*sin(x + 3*pi/2)*cos(-x + 2*pi)/(sin(x - pi)*cos(-x - pi)*cos(x + pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-x - pi) = sin(-x - pi) / cos(-x - pi),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(x + 3*pi/2) = -cos(x),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (x + 3*pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x - pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(x - pi) = -sin(pi - x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (x - pi) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + pi/2) = -sin(x),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_4_333_RAEI_extend(h0 : cos(pi/18) ≠ 0)  : (sqrt(3)*tan(pi/18) + 1)*(-sin(838*pi/9)**2 + sin(2207*pi/18)**2)=1:=
begin
have : (sqrt 3 * tan(pi / 18) + 1) * (-sin(838 * pi / 9) ** 2 + (-sin(2207 * pi / 18)) ** 2) = (sqrt(3)*tan(pi/18) + 1)*(-sin(838*pi/9)**2 + sin(2207*pi/18)**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(838*pi/9) = -sin(2207*pi/18),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (838*pi/9) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * tan(pi / 18) + 1) * (-sin(838 * pi / 9) ** 2 + cos(838 * pi / 9) ** 2) = (sqrt(3)*tan(pi/18) + 1)*(-sin(838*pi/9)**2 + cos(838*pi/9)**2),
{
field_simp at *,
},
have : cos(1676*pi/9) = -sin(838*pi/9) ** 2 + cos(838*pi/9) ** 2,
{
have : cos(1676*pi/9) = cos(2*(838*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * tan(pi / 18) + 1) * cos(1676 * pi / 9) = (sqrt(3)*tan(pi/18) + 1)*cos(1676*pi/9),
{
field_simp at *,
},
have : sin(5*pi/18) = cos(1676*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sqrt(3)*(sin(pi/18)/cos(pi/18)) + 1 = (sqrt(3)*sin(pi/18) + cos(pi/18))/cos(pi/18),
{
ring_exp,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
rw sin_pi_div_six,
have : sin(5*pi/18) = cos(2*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 2*sin(2*pi/9)/(2*(1/2)*cos(pi/18))*cos(2*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9)/(2*(1/2)*cos(pi/18)),
{
ring,
},
rw this,
have : 2*sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(4*pi/9) = cos(pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
end


lemma Trigo_4_334_CJGK_extend(h0 : cos(x - y) ≠ 0) (h1 : cos(x + y) ≠ 0)  (h2 : cos(x/2 - y/2)≠ 0) (h3 : (1-tan(x/2-y/2)**2)≠ 0) (h4 : (cos(2*x)/2+1/2-sin(y)**2)≠ 0) (h5 : (-sin(y)**2+cos(2*x)/2+1/2)≠ 0) (h6 : (-((-4)*sin(y/3)**3+3*sin(y/3))**2+cos(2*x)/2+1/2)≠ 0) (h7 : (-(-4*sin(y/3)**3+3*sin(y/3))**2+cos(2*x)/2+1/2)≠ 0) : tan(x + y) + 2*tan(x/2 - y/2)/(1 - tan(x/2 - y/2)**2)=sin(2*x)/(-(-4*sin(y/3)**3 + 3*sin(y/3))**2 + cos(2*x)/2 + 1/2):=
begin
have : sin(2 * x) / (-((-4) * sin(y / 3) ** 3 + 3 * sin(y / 3)) ** 2 + cos(2 * x) / 2 + 1 / 2) = sin(2*x)/(-(-4*sin(y/3)**3 + 3*sin(y/3))**2 + cos(2*x)/2 + 1/2),
{
field_simp at *,
},
have : sin(y) = -4 * sin(y/3) ** 3 + 3 * sin(y/3),
{
have : sin(y) = sin(3*(y/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : sin(2 * x) / (cos(2 * x) / 2 + 1 / 2 - sin(y) ** 2) = sin(2*x)/(-sin(y)**2 + cos(2*x)/2 + 1/2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : cos(x) ** 2 = cos(2*x) / 2 + 1 / 2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
conv {to_rhs, rw ← this,},
have : 2 * tan(x / 2 - y / 2) / (1 - tan(x / 2 - y / 2) ** 2) + tan(x + y) = tan(x + y) + 2*tan(x/2 - y/2)/(1 - tan(x/2 - y/2)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x - y) = 2 * tan(x/2 - y/2) / ( 1 - tan(x/2 - y/2) ** 2 ),
{
have : tan(x - y) = tan(2*(x/2 - y/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw tan_eq_sin_div_cos,
have : sin(x - y)/cos(x - y) + sin(x + y)/cos(x + y) = (sin(x - y)*cos(x + y) + sin(x + y)*cos(x - y))/(cos(x - y)*cos(x + y)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : sin(x - y)*cos(x + y) + sin(x + y)*cos(x - y) = sin(2*x),
{
have : sin(2*x) = sin((x + y) + (x - y)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add (x+y) (x-y),
ring,
},
rw this,
have : cos(x - y) = sin(x)*sin(y) + cos(x)*cos(y),
{
have : cos(x-y) = cos((x) - (y)),
{
apply congr_arg,
ring,
},
rw cos_sub,
ring,
},
rw this,
have : cos(x + y) = -sin(x)*sin(y) + cos(x)*cos(y),
{
have : cos(x+y) = cos((x) + (y)),
{
apply congr_arg,
ring,
},
rw cos_add,
ring,
},
rw this,
have : (sin(x)*sin(y) + cos(x)*cos(y))*(-sin(x)*sin(y) + cos(x)*cos(y)) = -sin(x)**2*sin(y)**2 + cos(x)**2*cos(y)**2,
{
ring_exp,
},
rw this,
rw cos_sq' y,
rw sin_sq x,
have : -(1 - cos(x)**2)*sin(y)**2 + cos(x)**2*(1 - sin(y)**2) = cos(x) ** 2 - sin(y) ** 2,
{
ring_exp,
},
rw this,
end


lemma Trigo_4_335_JVWS_extend(h0 : 1 - tan(5*pi/36) * tan(7*pi/36) ≠ 0) (h1 : cos(5*pi/36) ≠ 0) (h2 : cos(7*pi/36) ≠ 0)  (h3 : cos((7*pi/18)/2)≠ 0) (h4 : sin(7*pi/18)≠ 0) (h5 : -sin(277*pi/18)≠ 0) (h6 : sin(277*pi/18)≠ 0) (h7 : (sin(277*pi/18)*tan(2893*pi/36))≠ 0) (h8 : tan(2893*pi/36)≠ 0) : 1/tan(2893*pi/36) - sqrt(3)*(1 - cos(7*pi/18))/(sin(277*pi/18)*tan(2893*pi/36)) - (1 - cos(7*pi/18))/sin(277*pi/18)=sqrt(3):=
begin
have : 1 / tan(2893 * pi / 36) - sqrt 3 * (1 - cos(7 * pi / 18)) * (1 / tan(2893 * pi / 36)) / sin(277 * pi / 18) - (1 - cos(7 * pi / 18)) / sin(277 * pi / 18) = 1/tan(2893*pi/36) - sqrt(3)*(1 - cos(7*pi/18))/(sin(277*pi/18)*tan(2893*pi/36)) - (1 - cos(7*pi/18))/sin(277*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/36) = 1 / tan(2893*pi/36),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (5*pi/36) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5 * pi / 36) + sqrt 3 * (1 - cos(7 * pi / 18)) * tan(5 * pi / 36) / -sin(277 * pi / 18) + (1 - cos(7 * pi / 18)) / -sin(277 * pi / 18) = tan(5*pi/36) - sqrt(3)*(1 - cos(7*pi/18))*tan(5*pi/36)/sin(277*pi/18) - (1 - cos(7*pi/18))/sin(277*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = -sin(277*pi/18),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/18) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * tan(5 * pi / 36) * ((1 - cos(7 * pi / 18)) / sin(7 * pi / 18)) + tan(5 * pi / 36) + (1 - cos(7 * pi / 18)) / sin(7 * pi / 18) = tan(5*pi/36) + sqrt(3)*(1 - cos(7*pi/18))*tan(5*pi/36)/sin(7*pi/18) + (1 - cos(7*pi/18))/sin(7*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/36) = ( 1 - cos(7*pi/18) ) / sin(7*pi/18),
{
have : tan(7*pi/36) = tan((7*pi/18)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(5*pi/36) + tan(7*pi/36) = (-tan(5*pi/36)*tan(7*pi/36) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((5*pi/36) + (7*pi/36)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(5*pi/36)*tan(7*pi/36) + 1)*tan(pi/3) = -tan(5*pi/36)*tan(7*pi/36)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
ring_exp,
end


lemma Trigo_4_336_BNFJ_extend : -1 + cos(2587*pi/8)**2 + sin(pi/8)**2=-sqrt(2)/2:=
begin
have : cos(1387*pi/8) = cos(2587*pi/8),
{
rw cos_eq_cos_add_int_mul_two_pi (1387*pi/8) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(1 - sin(pi / 8) ** 2) + cos(1387 * pi / 8) ** 2 = -1 + cos(1387*pi/8)**2 + sin(pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/8) ** 2 = 1 - sin(pi/8) ** 2,
{
rw cos_sq',
},
conv {to_lhs, rw ← this,},
have : (-cos(1387 * pi / 8)) ** 2 - cos(pi / 8) ** 2 = -cos(pi/8)**2 + cos(1387*pi/8)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/8) = -cos(1387*pi/8),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/8) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_eq_neg_add,
have : -cos(pi/8)**2 + sin(pi/8)**2 = -cos(pi/4),
{
have : cos(pi/4) = -sin(pi/8)**2 + cos(pi/8)**2,
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
linarith,
},
rw this,
rw cos_pi_div_four,
ring_exp,
end


lemma Trigo_4_337_VMBT_extend(h0 : cos(pi/18) ≠ 0)  : (-sqrt(3) + tan(pi/18))*(-sin(2*pi)*cos(20*pi/9) + (1 - 2*(sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))**2)*sin(20*pi/9))=-1:=
begin
have : (-sqrt 3 + tan(pi / 18)) * (-sin(2 * pi) * cos(20 * pi / 9) + (1 - 2 * (sin(-pi) * cos(2 * pi) + sin(2 * pi) * cos(-pi)) ** 2) * sin(20 * pi / 9)) = (-sqrt(3) + tan(pi/18))*(-sin(2*pi)*cos(20*pi/9) + (1 - 2*(sin(-pi)*cos(2*pi) + sin(2*pi)*cos(-pi))**2)*sin(20*pi/9)),
{
field_simp at *,
},
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
have : (-sqrt 3 + tan(pi / 18)) * (-sin(2 * pi) * cos(20 * pi / 9) + sin(20 * pi / 9) * (1 - 2 * sin(pi) ** 2)) = (-sqrt(3) + tan(pi/18))*(-sin(2*pi)*cos(20*pi/9) + (1 - 2*sin(pi)**2)*sin(20*pi/9)),
{
field_simp at *,
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
have : (tan(pi / 18) - sqrt 3) * (sin(20 * pi / 9) * cos(2 * pi) - sin(2 * pi) * cos(20 * pi / 9)) = (-sqrt(3) + tan(pi/18))*(-sin(2*pi)*cos(20*pi/9) + sin(20*pi/9)*cos(2*pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = sin(20*pi/9) * cos(2*pi) - sin(2*pi) * cos(20*pi/9),
{
have : sin(2*pi/9) = sin((20*pi/9) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sin(pi/18)/cos(pi/18) - sqrt(3) = (-sqrt(3)*cos(pi/18) + sin(pi/18))/cos(pi/18),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw neg_mul,
have : sqrt(3)*cos(pi/18) = 2*sin(pi/3)*cos(pi/18),
{
field_simp,
ring_exp,
},
rw this,
have : sin(pi/18) = 2*sin(pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/3)*cos(pi/18) + 2*sin(pi/18)*cos(pi/3) = 2*sin(-5*pi/18),
{
have : sin(-5*pi/18) = sin(pi/18)*cos(pi/3) - sin(pi/3)*cos(pi/18),
{
have : sin(-5*pi/18) = sin((pi/18) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : sin(-5*pi/18) = -sin(5*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 2*-sin(5*pi/18)/cos(pi/18)*sin(2*pi/9) = -2*(sin(2*pi/9)*sin(5*pi/18))/cos(pi/18),
{
ring,
},
rw this,
have : sin(2*pi/9)*sin(5*pi/18) = -cos(pi/2)/2 + cos(-pi/18)/2,
{
rw sin_mul_sin,
have : cos((2*pi/9) + (5*pi/18)) = cos(pi/2),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi/9) - (5*pi/18)) = cos(-pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(-pi/18) = cos(pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_two,
norm_num,
field_simp,
end


lemma Trigo_4_338_BJHZ_extend : cos(2 + 133*pi) + 2*(-3*cos(1/3) + 4*cos(1/3)**3)**2 + 1=2:=
begin
have : 2 * ((-3) * cos(1 / 3) + 4 * cos(1 / 3) ** 3) ** 2 + 2 * (cos(2 + 133 * pi) / 2 + 1 / 2) = cos(2 + 133*pi) + 2*(-3*cos(1/3) + 4*cos(1/3)**3)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1 + 133*pi/2) ** 2 = cos(2 + 133*pi) / 2 + 1 / 2,
{
have : cos(2 + 133*pi) = cos(2*(1 + 133*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (4 * cos(1 / 3) ** 3 - 3 * cos(1 / 3)) ** 2 + 2 * cos(1 + 133 * pi / 2) ** 2 = 2*(-3*cos(1/3) + 4*cos(1/3)**3)**2 + 2*cos(1 + 133*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(1) = 4 * cos(1/3) ** 3 - 3 * cos(1/3),
{
have : cos(1) = cos(3*(1/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : 2 * (-cos(1 + 133 * pi / 2)) ** 2 + 2 * cos(1) ** 2 = 2*cos(1)**2 + 2*cos(1 + 133*pi/2)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1) = -cos(1 + 133*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (1) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1)**2 + cos(1)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
end


lemma Trigo_4_339_LVRV_extend(h0 : sin(5*pi/18) ≠ 0) (h1 : cos(5*pi/18) ≠ 0) (h2 : cos(pi/18) ≠ 0)  (h3 : -cos(625*pi/18)≠ 0) (h4 : cos(625*pi/18)≠ 0) (h5 : sin(5*pi/18)≠ 0) (h6 : (2*sin(5*pi/36)*cos(5*pi/36))≠ 0) (h7 : -sin(1208*pi/9)≠ 0) (h8 : sin(1208*pi/9)≠ 0) : 1/(2*sin(5*pi/36)*cos(5*pi/36)) + sqrt(3)/sin(1208*pi/9)=4:=
begin
have : 1 / (2 * sin(5 * pi / 36) * cos(5 * pi / 36)) - sqrt 3 / -sin(1208 * pi / 9) = 1/(2*sin(5*pi/36)*cos(5*pi/36)) + sqrt(3)/sin(1208*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(625*pi/18) = -sin(1208*pi/9),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (625*pi/18) (49),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 / (2 * sin(5 * pi / 36) * cos(5 * pi / 36)) - sqrt 3 / cos(625 * pi / 18) = 1/(2*sin(5*pi/36)*cos(5*pi/36)) - sqrt(3)/cos(625*pi/18),
{
field_simp at *,
},
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
have : sqrt 3 / -cos(625 * pi / 18) + 1 / sin(5 * pi / 18) = 1/sin(5*pi/18) - sqrt(3)/cos(625*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/18) = -cos(625*pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/18) (17),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3)/cos(5*pi/18) + 1/sin(5*pi/18) = (cos(5*pi/18) + sqrt(3)*sin(5*pi/18))/(sin(5*pi/18)*cos(5*pi/18)),
{
ring_exp,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : cos(5*pi/18) + sqrt(3)*sin(5*pi/18) = 2*sin(pi/6)*cos(5*pi/18) + 2*sin(5*pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : 2*sin(pi/6)*cos(5*pi/18) + 2*sin(5*pi/18)*cos(pi/6) = 2*sin(4*pi/9),
{
have : sin(4*pi/9) = sin(pi/6)*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6),
{
have : sin(4*pi/9) = sin((pi/6) + (5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
have : sin(5*pi/18)*cos(5*pi/18) = sin(5*pi/9)/2,
{
have : sin(5*pi/9) = 2*sin(5*pi/18)*cos(5*pi/18),
{
have : sin(5*pi/9) = sin(2*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/9) = cos(pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/9) = cos(pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_4_340_JESM_extend(h0 : cos(2*x) ≠ 0) (h1 : sin(2*x) + cos(2*x) ≠ 0)  (h2 : (sin(4*x+pi/2)*cos(-pi/2)+sin(-pi/2)*cos(4*x+pi/2)+cos(4*x)+1)≠ 0) (h3 : (sin(4*x+pi/2)*cos(-pi/2)+cos(4*x)+sin(-pi/2)*cos(4*x+pi/2)+1)≠ 0) (h4 : (-sin(-4*x+371*pi/2)*cos(-pi/2)+cos(4*x)+sin(-pi/2)*cos(4*x+pi/2)+1)≠ 0) (h5 : (-sin((-4)*x+371*pi/2)*cos(-pi/2)+cos(4*x)+sin(-pi/2)*cos(4*x+pi/2)+1)≠ 0) : (-sin(-4*x + 371*pi/2)*cos(-pi/2) - cos(4*x) + sin(-pi/2)*cos(4*x + pi/2) + 1)/(-sin(-4*x + 371*pi/2)*cos(-pi/2) + cos(4*x) + sin(-pi/2)*cos(4*x + pi/2) + 1)=-tan(-2*x + 32*pi):=
begin
have : -tan((-2) * x + 32 * pi) = -tan(-2*x + 32*pi),
{
field_simp at *,
},
have : tan(2*x) = -tan(-2*x + 32*pi),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*x) (32),
focus{repeat {apply congr_arg _}},
simp,
},
conv {to_rhs, rw ← this,},
have : (-sin((-4) * x + 371 * pi / 2) * cos(-pi / 2) - cos(4 * x) + sin(-pi / 2) * cos(4 * x + pi / 2) + 1) / (-sin((-4) * x + 371 * pi / 2) * cos(-pi / 2) + cos(4 * x) + sin(-pi / 2) * cos(4 * x + pi / 2) + 1) = (-sin(-4*x + 371*pi/2)*cos(-pi/2) - cos(4*x) + sin(-pi/2)*cos(4*x + pi/2) + 1)/(-sin(-4*x + 371*pi/2)*cos(-pi/2) + cos(4*x) + sin(-pi/2)*cos(4*x + pi/2) + 1),
{
field_simp at *,
},
have : sin(4*x + pi/2) = -sin(-4*x + 371*pi/2),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (4*x + pi/2) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(4 * x + pi / 2) * cos(-pi / 2) + sin(-pi / 2) * cos(4 * x + pi / 2) - cos(4 * x) + 1) / (sin(4 * x + pi / 2) * cos(-pi / 2) + sin(-pi / 2) * cos(4 * x + pi / 2) + cos(4 * x) + 1) = (sin(4*x + pi/2)*cos(-pi/2) - cos(4*x) + sin(-pi/2)*cos(4*x + pi/2) + 1)/(sin(4*x + pi/2)*cos(-pi/2) + cos(4*x) + sin(-pi/2)*cos(4*x + pi/2) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*x) = sin(4*x + pi/2) * cos(-pi/2) + sin(-pi/2) * cos(4*x + pi/2),
{
have : sin(4*x) = sin((4*x + pi/2) + (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*x) = -sin(2*x)**2 + cos(2*x)**2,
{
have : cos(4*x) = cos(2*(2*x)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : sin(4*x) - (-sin(2*x)**2 + cos(2*x)**2) + 1 = sin(4*x) - (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(4*x) - (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2) = sin(4*x) + 2*sin(2*x)**2,
{
ring,
},
rw this,
have : sin(4*x) + (-sin(2*x)**2 + cos(2*x)**2) + 1 = sin(4*x) + (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(4*x) + (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2) = sin(4*x) + 2*cos(2*x)**2,
{
ring,
},
rw this,
have : sin(4*x) = 2*sin(2*x)*cos(2*x),
{
have : sin(4*x) = sin(2*(2*x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : 2*sin(2*x)*cos(2*x) + 2*sin(2*x)**2 = 2*sin(2*x)*(sin(2*x) + cos(2*x)),
{
ring_exp,
},
rw this,
have : 2*sin(2*x)*cos(2*x) + 2*cos(2*x)**2 = 2*cos(2*x)*(sin(2*x) + cos(2*x)),
{
ring_exp,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring_exp,
end


lemma Trigo_4_341_YKKV_extend(h0 : cos(x) ≠ 0) (h1 : sin(x) ≠ 0)  (h2 : (sin(-x+3*pi/2)*sin(x+40*pi))≠ 0) (h3 : (sin(x+40*pi)*sin(-x+3*pi/2))≠ 0) (h4 : (sin(x+3*pi/2)*cos(x+2*pi))≠ 0) (h5 : (sin(-x+249*pi/2)*sin(x+3*pi/2))≠ 0) (h6 : (sin(x+3*pi/2)*sin(-x+249*pi/2))≠ 0) : (-sin(x/2 - 7*pi/4)**2 + cos(x/2 - 7*pi/4)**2)*sin(-x + 2*pi)/(sin(-x + 249*pi/2)*sin(x + 3*pi/2)) + tan(-x + 3*pi)/(sin(-x + 3*pi/2)*sin(x + 40*pi))=1:=
begin
have : (-sin(x / 2 - 7 * pi / 4) ** 2 + cos(x / 2 - 7 * pi / 4) ** 2) * sin(-x + 2 * pi) / (sin(x + 3 * pi / 2) * sin(-x + 249 * pi / 2)) + tan(-x + 3 * pi) / (sin(-x + 3 * pi / 2) * sin(x + 40 * pi)) = (-sin(x/2 - 7*pi/4)**2 + cos(x/2 - 7*pi/4)**2)*sin(-x + 2*pi)/(sin(-x + 249*pi/2)*sin(x + 3*pi/2)) + tan(-x + 3*pi)/(sin(-x + 3*pi/2)*sin(x + 40*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 2*pi) = sin(-x + 249*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (x + 2*pi) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2 * pi) * (-sin(x / 2 - 7 * pi / 4) ** 2 + cos(x / 2 - 7 * pi / 4) ** 2) / (sin(x + 3 * pi / 2) * cos(x + 2 * pi)) + tan(-x + 3 * pi) / (sin(-x + 3 * pi / 2) * sin(x + 40 * pi)) = (-sin(x/2 - 7*pi/4)**2 + cos(x/2 - 7*pi/4)**2)*sin(-x + 2*pi)/(sin(x + 3*pi/2)*cos(x + 2*pi)) + tan(-x + 3*pi)/(sin(-x + 3*pi/2)*sin(x + 40*pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x - 7*pi/2) = -sin(x/2 - 7*pi/4) ** 2 + cos(x/2 - 7*pi/4) ** 2,
{
have : cos(x - 7*pi/2) = cos(2*(x/2 - 7*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2 * pi) * cos(x - 7 * pi / 2) / (sin(x + 3 * pi / 2) * cos(x + 2 * pi)) + tan(-x + 3 * pi) / (sin(x + 40 * pi) * sin(-x + 3 * pi / 2)) = sin(-x + 2*pi)*cos(x - 7*pi/2)/(sin(x + 3*pi/2)*cos(x + 2*pi)) + tan(-x + 3*pi)/(sin(-x + 3*pi/2)*sin(x + 40*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x + 40*pi),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 2*pi) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x - 7*pi/2) = cos(-x + 7*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x - 7*pi/2) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 7*pi/2) = -cos(-x + pi/2),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-x + 7*pi/2) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + pi/2) = sin(x),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(x + 3*pi/2) = -sin(x + pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + 3*pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(x + 2*pi) = cos(x),
{
rw cos_eq_cos_add_int_mul_two_pi (x + 2*pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(-x + 3*pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x + 3*pi) (3),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x + 3*pi/2) = -sin(-x + pi/2),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-x + 3*pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-x + pi/2) = cos(x),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
rw tan_eq_sin_div_cos,
have : -sin(x)*-sin(x)/(-cos(x)*cos(x)) + -(sin(x)/cos(x))/(sin(x)*-cos(x)) = (1 - sin(x)**2)/cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw sin_sq,
norm_num,
field_simp,
end


lemma Trigo_4_342_JEBY_extend (h0 : sin(142*pi/3)≠ 0) (h1 : (4*sin(142*pi/3))≠ 0) (h2 : (2*sin(142*pi/3))≠ 0) : -cos(287*pi/6)/2 - sin(284*pi/3)/(4*sin(142*pi/3)) + sin(pi/4)*cos(pi/12)=1/2:=
begin
have : -cos(287 * pi / 6) / 2 - sin(284 * pi / 3) / (2 * sin(142 * pi / 3)) / 2 + sin(pi / 4) * cos(pi / 12) = -cos(287*pi/6)/2 - sin(284*pi/3)/(4*sin(142*pi/3)) + sin(pi/4)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(142*pi/3) = sin(284*pi/3) / ( 2 * sin(142*pi/3) ),
{
have : sin(284*pi/3) = sin(2*(142*pi/3)),
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
have : -(cos(142 * pi / 3) / 2 + cos(287 * pi / 6) / 2) + sin(pi / 4) * cos(pi / 12) = -cos(287*pi/6)/2 - cos(142*pi/3)/2 + sin(pi/4)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(571*pi/12) * cos(pi/4) = cos(142*pi/3) / 2 + cos(287*pi/6) / 2,
{
rw cos_mul_cos,
have : cos((571*pi/12) + (pi/4)) = cos(287*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : cos((571*pi/12) - (pi/4)) = cos(142*pi/3),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(cos(571*pi/12) * cos(pi/4)) = -cos(pi/4)*cos(571*pi/12),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(pi / 4) * cos(pi / 12) - cos(571 * pi / 12) * cos(pi / 4) = -cos(pi/4)*cos(571*pi/12) + sin(pi/4)*cos(pi/12),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/12) = cos(571*pi/12),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/12) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/12) = sin(pi/12),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sub_eq_neg_add,
rw ← neg_mul,
have : -sin(pi/12)*cos(pi/4) + sin(pi/4)*cos(pi/12) = sin(pi/6),
{
have : sin(pi/6) = sin((pi/4) - (pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_4_343_QYWS_extend(h0 : sin(x) ≠ 0)  (h1 : tan(x)≠ 0) (h2 : sin(x)≠ 0) (h3 : (2*sin(x/2)*cos(x/2))≠ 0) : (1/tan(x) + 1/(2*sin(x/2)*cos(x/2)))*(-4*(sin(-pi)*sin(x/3 - pi) + cos(-pi)*cos(x/3 - pi))**3 + 3*sin(-pi)*sin(x/3 - pi) + 3*cos(-pi)*cos(x/3 - pi) + 1)=sin(x):=
begin
have : (1 / tan(x) + 1 / (2 * sin(x / 2) * cos(x / 2))) * ((-4) * (sin(x / 3 - pi) * sin(-pi) + cos(x / 3 - pi) * cos(-pi)) ** 3 + 3 * (sin(x / 3 - pi) * sin(-pi) + cos(x / 3 - pi) * cos(-pi)) + 1) = (1/tan(x) + 1/(2*sin(x/2)*cos(x/2)))*(-4*(sin(-pi)*sin(x/3 - pi) + cos(-pi)*cos(x/3 - pi))**3 + 3*sin(-pi)*sin(x/3 - pi) + 3*cos(-pi)*cos(x/3 - pi) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x/3) = sin(x/3 - pi) * sin(-pi) + cos(x/3 - pi) * cos(-pi),
{
have : cos(x/3) = cos((x/3 - pi) - (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 / tan(x) + 1 / (2 * sin(x / 2) * cos(x / 2))) * ((-4) * cos(x / 3) ** 3 + 3 * cos(x / 3) + 1) = (1/tan(x) + 1/(2*sin(x/2)*cos(x/2)))*(-4*cos(x/3)**3 + 3*cos(x/3) + 1),
{
field_simp at *,
},
have : sin(x) = 2 * sin(x/2) * cos(x/2),
{
have : sin(x) = sin(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : (1 - (4 * cos(x / 3) ** 3 - 3 * cos(x / 3))) * (1 / tan(x) + 1 / sin(x)) = (1/tan(x) + 1/sin(x))*(-4*cos(x/3)**3 + 3*cos(x/3) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = 4 * cos(x/3) ** 3 - 3 * cos(x/3),
{
have : cos(x) = cos(3*(x/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw one_div_div,
have : cos(x)/sin(x) + 1/sin(x) = (cos(x) + 1)/sin(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
rw mul_div_assoc',
have : (1 - cos(x))*(cos(x) + 1) = 1 - cos(x)**2,
{
ring_exp,
},
rw this,
rw ← sin_sq,
field_simp,
ring_exp,
end


lemma Trigo_4_344_QPKD_extend(h0 : sin(pi/15) ≠ 0)  : (-1 + 2*cos(pi/15)**2)*(-4*sin(13*pi/90)**3 + 3*sin(13*pi/90))*sin(pi/30)*cos(4*pi/15)=1/16:=
begin
have : (-(1 - cos(pi / 15) ** 2) + cos(pi / 15) ** 2) * ((-4) * sin(13 * pi / 90) ** 3 + 3 * sin(13 * pi / 90)) * sin(pi / 30) * cos(4 * pi / 15) = (-1 + 2*cos(pi/15)**2)*(-4*sin(13*pi/90)**3 + 3*sin(13*pi/90))*sin(pi/30)*cos(4*pi/15),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/15) ** 2 = 1 - cos(pi/15) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi / 15) ** 2 + cos(pi / 15) ** 2) * sin(pi / 30) * ((-4) * sin(13 * pi / 90) ** 3 + 3 * sin(13 * pi / 90)) * cos(4 * pi / 15) = (-sin(pi/15)**2 + cos(pi/15)**2)*(-4*sin(13*pi/90)**3 + 3*sin(13*pi/90))*sin(pi/30)*cos(4*pi/15),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/30) = -4 * sin(13*pi/90) ** 3 + 3 * sin(13*pi/90),
{
have : sin(13*pi/30) = sin(3*(13*pi/90)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 30) * sin(13 * pi / 30) * (-sin(pi / 15) ** 2 + cos(pi / 15) ** 2) * cos(4 * pi / 15) = (-sin(pi/15)**2 + cos(pi/15)**2)*sin(pi/30)*sin(13*pi/30)*cos(4*pi/15),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/15) = -sin(pi/15) ** 2 + cos(pi/15) ** 2,
{
have : cos(2*pi/15) = cos(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/30) = cos(7*pi/15),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/30) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(13*pi/30) = cos(pi/15),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/30) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/15) = sin(2*pi/15)/(2*sin(pi/15)),
{
have : sin(2*pi/15) = sin(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : cos(7*pi/15)*(sin(2*pi/15)/(2*sin(pi/15)))*cos(2*pi/15)*cos(4*pi/15) = sin(2*pi/15)*cos(2*pi/15)*cos(4*pi/15)*cos(7*pi/15)/(2*sin(pi/15)),
{
ring,
},
rw this,
have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
{
have : sin(4*pi/15) = 2*sin(2*pi/15)*cos(2*pi/15),
{
have : sin(4*pi/15) = sin(2*(2*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/15)/2*cos(4*pi/15) = sin(4*pi/15)*cos(4*pi/15)/2,
{
ring,
},
rw this,
have : sin(4*pi/15)*cos(4*pi/15) = sin(8*pi/15)/2,
{
have : sin(8*pi/15) = 2*sin(4*pi/15)*cos(4*pi/15),
{
have : sin(8*pi/15) = sin(2*(4*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(7*pi/15) = -cos(8*pi/15),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (7*pi/15) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(8*pi/15)/2/2*-cos(8*pi/15) = -(sin(8*pi/15)*cos(8*pi/15)/2/2),
{
ring,
},
rw this,
have : sin(8*pi/15)*cos(8*pi/15) = sin(16*pi/15)/2,
{
have : sin(16*pi/15) = 2*sin(8*pi/15)*cos(8*pi/15),
{
have : sin(16*pi/15) = sin(2*(8*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(16*pi/15) = -sin(pi/15),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (16*pi/15) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_4_345_DSOO_extend : -sin(3169*pi/18)/2 + sin(523*pi/3)/2 - (sin(pi/3)*sin(59*pi/36) + cos(pi/3)*cos(59*pi/36))*cos(5*pi/36)=sqrt(3)/2:=
begin
have : -(-sin(523 * pi / 3) / 2 + sin(3169 * pi / 18) / 2) - (sin(pi / 3) * sin(59 * pi / 36) + cos(pi / 3) * cos(59 * pi / 36)) * cos(5 * pi / 36) = -sin(3169*pi/18)/2 + sin(523*pi/3)/2 - (sin(pi/3)*sin(59*pi/36) + cos(pi/3)*cos(59*pi/36))*cos(5*pi/36),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(31*pi/36) * cos(6307*pi/36) = -sin(523*pi/3) / 2 + sin(3169*pi/18) / 2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((6307*pi/36) + (31*pi/36)) = sin(3169*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : sin((6307*pi/36) - (31*pi/36)) = sin(523*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(31*pi/36) * cos(6307*pi/36)) = -sin(31*pi/36)*cos(6307*pi/36),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(31 * pi / 36) * -cos(6307 * pi / 36) - (sin(pi / 3) * sin(59 * pi / 36) + cos(pi / 3) * cos(59 * pi / 36)) * cos(5 * pi / 36) = -sin(31*pi/36)*cos(6307*pi/36) - (sin(pi/3)*sin(59*pi/36) + cos(pi/3)*cos(59*pi/36))*cos(5*pi/36),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/36) = -cos(6307*pi/36),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (7*pi/36) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(31 * pi / 36) * cos(7 * pi / 36) - cos(5 * pi / 36) * (sin(59 * pi / 36) * sin(pi / 3) + cos(59 * pi / 36) * cos(pi / 3)) = sin(31*pi/36)*cos(7*pi/36) - (sin(pi/3)*sin(59*pi/36) + cos(pi/3)*cos(59*pi/36))*cos(5*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(47*pi/36) = sin(59*pi/36) * sin(pi/3) + cos(59*pi/36) * cos(pi/3),
{
have : cos(47*pi/36) = cos((59*pi/36) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(31*pi/36) = sin(5*pi/36),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (31*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(47*pi/36) = -cos(11*pi/36),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (47*pi/36) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(11*pi/36) = sin(7*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_neg,
rw sub_eq_add_neg,
rw neg_neg,
rw mul_comm (cos(5*pi/36)) (sin(7*pi/36)),
have : sin(5*pi/36)*cos(7*pi/36) + sin(7*pi/36)*cos(5*pi/36) = sin(pi/3),
{
have : sin(pi/3) = sin((5*pi/36) + (7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw sin_pi_div_three,
end


lemma Trigo_4_346_HJNU_extend(h0 : cos(19*pi/180) ≠ 0) (h1 : cos(11*pi/180) ≠ 0) (h2 : 1-tan(11*pi/180)*tan(19*pi/180) ≠ 0) (h3 : tan((11*pi/180)+(19*pi/180)) ≠ 0)  (h4 : cos(11*pi/180)≠ 0) (h5 : (cos(11*pi/180)*tan(14869*pi/180))≠ 0) (h6 : tan(14869*pi/180)≠ 0) : -cos(3881*pi/180)/(cos(11*pi/180)*tan(14869*pi/180)) + sqrt(3)*cos(3881*pi/180)/cos(11*pi/180) - sqrt(3)/tan(14869*pi/180)=1:=
begin
have : -cos(3881 * pi / 180) / (cos(11 * pi / 180) * tan(14869 * pi / 180)) + sqrt 3 * cos(3881 * pi / 180) / cos(11 * pi / 180) - sqrt 3 / tan(14869 * pi / 180) = -cos(3881*pi/180)/(cos(11*pi/180)*tan(14869*pi/180)) + sqrt(3)*cos(3881*pi/180)/cos(11*pi/180) - sqrt(3)/tan(14869*pi/180),
{
field_simp at *,
},
have : sin(11*pi/180) = cos(3881*pi/180),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (11*pi/180) (10),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11 * pi / 180) * ((-1) / tan(14869 * pi / 180)) / cos(11 * pi / 180) + sqrt 3 * sin(11 * pi / 180) / cos(11 * pi / 180) + sqrt 3 * ((-1) / tan(14869 * pi / 180)) = -sin(11*pi/180)/(cos(11*pi/180)*tan(14869*pi/180)) + sqrt(3)*sin(11*pi/180)/cos(11*pi/180) - sqrt(3)/tan(14869*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(19*pi/180) = -1 / tan(14869*pi/180),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (19*pi/180) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11 * pi / 180) / cos(11 * pi / 180) * tan(19 * pi / 180) + sqrt 3 * (sin(11 * pi / 180) / cos(11 * pi / 180)) + sqrt 3 * tan(19 * pi / 180) = sin(11*pi/180)*tan(19*pi/180)/cos(11*pi/180) + sqrt(3)*sin(11*pi/180)/cos(11*pi/180) + sqrt(3)*tan(19*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/180) = sin(11*pi/180) / cos(11*pi/180),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/180)*tan(19*pi/180) = -(tan(11*pi/180) + tan(19*pi/180))/tan(pi/6) + 1,
{
rw tan_mul_tan',
have : tan((11*pi/180) + (19*pi/180)) = tan(pi/6),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
rw this,
rw tan_pi_div_six,
rw sqrt_div_self,
field_simp,
ring_exp,
end


lemma Trigo_4_347_ZWTX_extend(h0 : 1 - tan(x/2) ≠ 0) (h1 : cos(pi/4) ≠ 0) (h2 : cos(x/2) ≠ 0) (h3 : 1 + tan(x/2) ≠ 0) (h3 : tan(x/2) + 1 ≠ 0) (h4 : -tan(x/2) + 1 ≠ 0) (h6 : tan(-x/2+65*pi/4)≠ 0) (h7 : cos((-x + 65*pi/2)/2)≠ 0) (h8 : sin(-x+65*pi/2)≠ 0) (h9 : ((1-cos(-x+65*pi/2))/sin(-x+65*pi/2))≠ 0) (h10 : (1-cos(-x+65*pi/2))≠ 0) : -tan(-x/2 + 49*pi/4) + sin(-x + 65*pi/2)/(1 - cos(-x + 65*pi/2))=2*tan(x):=
begin
have : -tan(-x / 2 + 49 * pi / 4) + 1 / ((1 - cos(-x + 65 * pi / 2)) / sin(-x + 65 * pi / 2)) = -tan(-x/2 + 49*pi/4) + sin(-x + 65*pi/2)/(1 - cos(-x + 65*pi/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(-x/2 + 65*pi/4) = ( 1 - cos(-x + 65*pi/2) ) / sin(-x + 65*pi/2),
{
have : tan(-x/2 + 65*pi/4) = tan((-x + 65*pi/2)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(x/2 - pi/4) = -tan(-x/2 + 49*pi/4),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (x/2 - pi/4) (12),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x/2 + pi/4) = 1 / tan(-x/2 + 65*pi/4),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (x/2 + pi/4) (16),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x/2 - pi/4) = (tan(x/2) - tan(pi/4))/(tan(pi/4)*tan(x/2) + 1),
{
have : tan(x/2 - pi/4) = tan((x/2) - (pi/4)),
{
apply congr_arg,
ring,
},
rw tan_sub,
field_simp,
left,
ring_exp,
repeat {assumption},
},
rw this,
have : tan(x/2 + pi/4) = (tan(x/2) + tan(pi/4))/(-tan(pi/4)*tan(x/2) + 1),
{
have : tan(x/2 + pi/4) = tan((x/2) + (pi/4)),
{
apply congr_arg,
ring,
},
rw tan_add,
field_simp,
left,
ring_exp,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
have : (tan(x/2) - 1)/(1*tan(x/2) + 1) + (tan(x/2) + 1)/(-1*tan(x/2) + 1) = ((1 - tan(x/2))*(tan(x/2) - 1) + (tan(x/2) + 1)**2)/((1 - tan(x/2))*(tan(x/2) + 1)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : (1 - tan(x/2))*(tan(x/2) - 1) = -tan(x/2)**2 + 2*tan(x/2) - 1,
{
ring_exp,
},
rw this,
have : (tan(x/2) + 1)**2 = tan(x/2)**2 + 2*tan(x/2) + 1,
{
ring_exp,
},
rw this,
have : (1 - tan(x/2))*(tan(x/2) + 1) = 1 - tan(x/2)**2,
{
ring_exp,
},
rw this,
have : (-tan(x/2)**2 + 2*tan(x/2) - 1 + (tan(x/2)**2 + 2*tan(x/2) + 1)) = 4*tan(x/2),
{
ring,
},
rw this,
have : 4*tan(x/2)/(1 - tan(x/2)**2) = 2*tan(x),
{
have : tan(x) = 2*tan(x/2)/(1 - tan(x/2)**2),
{
have : tan(x) = tan(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
rw this,
ring_exp,
},
rw this, 
end


lemma Trigo_4_348_WZTA_extend(h0 : cos(7*pi/45) ≠ 0) (h1 : 1 - tan(7*pi/45) * tan(17*pi/180) ≠ 0) (h2 : cos(17*pi/180) ≠ 0)  (h3 : tan(7633*pi/180)≠ 0) (h4 : cos((7633*pi/90)/2)≠ 0) (h5 : (1-cos(7633*pi/90))≠ 0) (h6 : ((1-cos(7633*pi/90))/sin(7633*pi/90))≠ 0) (h7 : sin(7633*pi/90)≠ 0) : (-sin(10963*pi/90)/(1 - cos(7633*pi/90)) + 1)*(tan(7*pi/45) + 1)=2:=
begin
have : sin(7633*pi/90) = -sin(10963*pi/90),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7633*pi/90) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(7 * pi / 45) + 1) * (1 / ((1 - cos(7633 * pi / 90)) / sin(7633 * pi / 90)) + 1) = (sin(7633*pi/90)/(1 - cos(7633*pi/90)) + 1)*(tan(7*pi/45) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7633*pi/180) = ( 1 - cos(7633*pi/90) ) / sin(7633*pi/90),
{
have : tan(7633*pi/180) = tan((7633*pi/90)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (1 / tan(7633 * pi / 180) + 1) * (tan(7 * pi / 45) + 1) = (tan(7*pi/45) + 1)*(1/tan(7633*pi/180) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(17*pi/180) = 1 / tan(7633*pi/180),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (17*pi/180) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(17*pi/180) + 1)*(tan(7*pi/45) + 1) = tan(17*pi/180)*tan(7*pi/45) + tan(17*pi/180) + tan(7*pi/45) + 1,
{
ring_exp,
},
rw this,
have : tan(17*pi/180)*tan(7*pi/45) + tan(17*pi/180) + tan(7*pi/45) + 1 = tan(17*pi/180)*tan(7*pi/45) + (tan(17*pi/180) + tan(7*pi/45)) + 1,
{
ring,
},
rw this,
have : tan(17*pi/180) + tan(7*pi/45) = (-tan(17*pi/180)*tan(7*pi/45) + 1)*tan(pi/4),
{
rw add_comm,
rw tan_add_tan,
have : tan((7*pi/45) + (17*pi/180)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_4_349_KYZD_extend(h0 : cos(pi/4) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : sin(x) + cos(x) ≠ 0) (h3 : cos(2*x) ≠ 0) (h4 : (2*sin(x+pi/4)**2*tan(-x+pi/4))≠ 0) (h5 : (2*(sin(x+9*pi/4)*cos((-2)*pi)+sin((-2)*pi)*cos(x+9*pi/4))**2*tan(-x+pi/4))≠ 0) (h6 : (2*(sin(x+9*pi/4)*cos(-2*pi)+sin(-2*pi)*cos(x+9*pi/4))**2*tan(-x+pi/4))≠ 0) (h7 : (2*(sin(x+9*pi/4)*cos((-2)*pi)+sin((-2)*pi)*(-sin(x+31*pi/12)*sin(-pi/3)+cos(x+31*pi/12)*cos(-pi/3)))**2*tan(-x+pi/4))≠ 0) (h8 : (2*((-sin(-pi/3)*sin(x+31*pi/12)+cos(-pi/3)*cos(x+31*pi/12))*sin(-2*pi)+sin(x+9*pi/4)*cos(-2*pi))**2*tan(-x+pi/4))≠ 0) : cos(2*x)/(2*((-sin(-pi/3)*sin(x + 31*pi/12) + cos(-pi/3)*cos(x + 31*pi/12))*sin(-2*pi) + sin(x + 9*pi/4)*cos(-2*pi))**2*tan(-x + pi/4))=1:=
begin
have : cos(2 * x) / (2 * (sin(x + 9 * pi / 4) * cos((-2) * pi) + sin((-2) * pi) * (-sin(x + 31 * pi / 12) * sin(-pi / 3) + cos(x + 31 * pi / 12) * cos(-pi / 3))) ** 2 * tan(-x + pi / 4)) = cos(2*x)/(2*((-sin(-pi/3)*sin(x + 31*pi/12) + cos(-pi/3)*cos(x + 31*pi/12))*sin(-2*pi) + sin(x + 9*pi/4)*cos(-2*pi))**2*tan(-x + pi/4)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x + 9*pi/4) = -sin(x + 31*pi/12) * sin(-pi/3) + cos(x + 31*pi/12) * cos(-pi/3),
{
have : cos(x + 9*pi/4) = cos((x + 31*pi/12) + (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2 * x) / (2 * (sin(x + 9 * pi / 4) * cos((-2) * pi) + sin((-2) * pi) * cos(x + 9 * pi / 4)) ** 2 * tan(-x + pi / 4)) = cos(2*x)/(2*(sin(x + 9*pi/4)*cos(-2*pi) + sin(-2*pi)*cos(x + 9*pi/4))**2*tan(-x + pi/4)),
{
field_simp at *,
},
have : sin(x + pi/4) = sin(x + 9*pi/4) * cos(-2*pi) + sin(-2*pi) * cos(x + 9*pi/4),
{
have : sin(x + pi/4) = sin((x + 9*pi/4) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * (cos(2 * x) / 2 + 1 / 2) - 1) / (2 * sin(x + pi / 4) ** 2 * tan(-x + pi / 4)) = cos(2*x)/(2*sin(x + pi/4)**2*tan(-x + pi/4)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) ** 2 = cos(2*x) / 2 + 1 / 2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*sin(x + pi/4)**2 = 1 - cos(2*x + pi/2),
{
have : sin(x + pi/4)**2 = 1/2 - cos(2*x + pi/2)/2,
{
have : cos(2*x + pi/2) = cos(2*(x + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
linarith,
},
rw this,
have : cos(2*x + pi/2) = -sin(pi/2)*sin(2*x) + cos(pi/2)*cos(2*x),
{
have : cos(2*x+pi/2) = cos((pi/2) + (2*x)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
rw cos_pi_div_two,
rw sin_pi_div_two,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
simp,
have : 1 + 2*sin(x)*cos(x) = sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x) = (sin(x) + cos(x))**2,
{
ring_exp,
},
rw this,
have : tan(-x + pi/4) = (-tan(x) + tan(pi/4))/(tan(pi/4)*tan(x) + 1),
{
have : tan(-x + pi/4) = tan((pi/4) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
field_simp,
ring_exp,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
rw tan_eq_sin_div_cos,
have : 1*(sin(x)/cos(x)) + 1 = (sin(x) + cos(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : -(sin(x)/cos(x)) + 1 = (-sin(x) + cos(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : (sin(x) + cos(x))**2*((-sin(x) + cos(x))/cos(x)/((sin(x) + cos(x))/cos(x))) = (sin(x) + cos(x))*(-sin(x) + cos(x)),
{
field_simp,
ring_exp,
},
rw this,
have :(sin(x) + cos(x))*(-sin(x) + cos(x)) = -sin(x)**2 + cos(x)**2,
{
ring_exp,
},
rw this,
have : -sin(x)**2 + cos(x)**2 = cos(2*x),
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
have : 2*cos(x)**2 - 1 = cos(2*x),
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul,
},
rw this,
field_simp,
end


lemma Trigo_5_350_KKXN_extend(h0 : cos(23*pi/180) ≠ 0) (h1 : cos(11*pi/90) ≠ 0) (h2 : 1 - tan(11*pi/90) * tan(23*pi/180) ≠ 0)  (h3 : cos(11*pi/180)≠ 0) (h4 : (1-tan(11*pi/180)**2)≠ 0) (h5 : (1-tan(13871*pi/180)**2)≠ 0) : -2*tan(13871*pi/180)*tan(14017*pi/180)/(1 - tan(13871*pi/180)**2) + 2*tan(13871*pi/180)/(1 - tan(13871*pi/180)**2) - tan(14017*pi/180)=1:=
begin
have : 2 * -tan(14017 * pi / 180) * tan(13871 * pi / 180) / (1 - tan(13871 * pi / 180) ** 2) + 2 * tan(13871 * pi / 180) / (1 - tan(13871 * pi / 180) ** 2) + -tan(14017 * pi / 180) = -2*tan(13871*pi/180)*tan(14017*pi/180)/(1 - tan(13871*pi/180)**2) + 2*tan(13871*pi/180)/(1 - tan(13871*pi/180)**2) - tan(14017*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(23*pi/180) = -tan(14017*pi/180),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (23*pi/180) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * tan(13871 * pi / 180) * tan(23 * pi / 180) / (1 - tan(13871 * pi / 180) ** 2) + 2 * tan(13871 * pi / 180) / (1 - tan(13871 * pi / 180) ** 2) + tan(23 * pi / 180) = 2*tan(23*pi/180)*tan(13871*pi/180)/(1 - tan(13871*pi/180)**2) + 2*tan(13871*pi/180)/(1 - tan(13871*pi/180)**2) + tan(23*pi/180),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/180) = tan(13871*pi/180),
{
rw tan_eq_tan_add_int_mul_pi (11*pi/180) (77),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * tan(11 * pi / 180) / (1 - tan(11 * pi / 180) ** 2) * tan(23 * pi / 180) + 2 * tan(11 * pi / 180) / (1 - tan(11 * pi / 180) ** 2) + tan(23 * pi / 180) = 2*tan(11*pi/180)*tan(23*pi/180)/(1 - tan(11*pi/180)**2) + 2*tan(11*pi/180)/(1 - tan(11*pi/180)**2) + tan(23*pi/180),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/90) = 2 * tan(11*pi/180) / ( 1 - tan(11*pi/180) ** 2 ),
{
have : tan(11*pi/90) = tan(2*(11*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(11*pi/90) + tan(23*pi/180) = (-tan(11*pi/90)*tan(23*pi/180) + 1)*tan(pi/4),
{
rw tan_add_tan,
have : tan((11*pi/90) + (23*pi/180)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_5_351_AIJZ_extend(h0 : 2 ≠ 0) (h1 : 2*sin(x)*cos(x) + 2*cos(x) ≠ 0) (h2 : sin(x)/2 + 1/2 ≠ 0) (h3 : sin(x) + 1 ≠ 0) (h4 : 1 + sin(x) ≠ 0) (h5 : cos(-x/2+pi/4)≠ 0) (h6 : (sin(2*x)+2*sin(x+141*pi/2))≠ 0) (h7 : (2*sin(x+141*pi/2)-cos(2*x+221*pi/2))≠ 0) (h8 : (-cos(2*x+221*pi/2)+2*sin(x+141*pi/2))≠ 0) : (2*sin(x + 141*pi/2) + cos(2*x + 221*pi/2))/(2*sin(x + 141*pi/2) - cos(2*x + 221*pi/2))=sin(-x/2 + pi/4)**2/cos(-x/2 + pi/4)**2:=
begin
have : (- -cos(2 * x + 221 * pi / 2) + 2 * sin(x + 141 * pi / 2)) / (-cos(2 * x + 221 * pi / 2) + 2 * sin(x + 141 * pi / 2)) = (2*sin(x + 141*pi/2) + cos(2*x + 221*pi/2))/(2*sin(x + 141*pi/2) - cos(2*x + 221*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x) = -cos(2*x + 221*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*x) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(x + 141*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(-x / 2 + pi / 4) / cos(-x / 2 + pi / 4)) ** 2 = sin(-x/2 + pi/4)**2/cos(-x/2 + pi/4)**2,
{
field_simp at *,
},
conv {to_rhs, rw ← this,},
have : tan(-x/2 + pi/4) = sin(-x/2 + pi/4) / cos(-x/2 + pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_rhs, rw ← this,},
have : -sin(2*x) = -2*sin(x)*cos(x),
{
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
have : (-2*sin(x)*cos(x) + 2*cos(x))/(2*sin(x)*cos(x) + 2*cos(x)) = (1 - sin(x))/(sin(x) + 1),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw tan_eq_sin_div_cos,
rw div_pow,
have : sin(-x/2 + pi/4)**2 = 1/2 - cos(-x+pi/2)/2,
{
have : cos(-x + pi/2) = cos(2*(-x/2 + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(-x/2 + pi/4)**2 = 1/2 + cos(-x+pi/2)/2,
{
have : cos(-x + pi/2) = cos(2*(-x/2 + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
have : cos(-x+pi/2) = sin(x),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_352_IIIT_extend : -2*cos(x + 371*pi/2)*cos(x + y) - cos(2*x + y + 141*pi/2)=sin(y):=
begin
have : -cos(2 * x + y + 141 * pi / 2) - 2 * cos(x + 371 * pi / 2) * cos(x + y) = -2*cos(x + 371*pi/2)*cos(x + y) - cos(2*x + y + 141*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x + y + 48*pi) = -cos(2*x + y + 141*pi/2),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (2*x + y + 48*pi) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x + y) = sin(2*x + y + 48*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (2*x + y) (24),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * cos(x + 371 * pi / 2) * cos(x + y) + sin(2 * x + y) = sin(2*x + y) - 2*cos(x + 371*pi/2)*cos(x + y),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = cos(x + 371*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + y) = -sin(x)*sin(y) + cos(x)*cos(y),
{
have : cos(x+y) = cos((x) + (y)),
{
apply congr_arg,
ring,
},
rw cos_add,
ring,
},
rw this,
have : sin(2*x + y) = sin(2*x)*cos(y) + sin(y)*cos(2*x),
{
have : sin(2*x+y) = sin((y) + (2*x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
have : cos(2*x) = 1 - 2*sin(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul'',
},
rw this,
have : sin(y)*(1 - 2*sin(x)**2) = -2*sin(x)**2*sin(y) + sin(y),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw mul_assoc,
have : sin(x)*(-sin(x)*sin(y) + cos(x)*cos(y)) = -sin(x)**2*sin(y) + sin(x)*cos(x)*cos(y),
{
ring_exp,
},
rw this,
norm_num,
ring_exp,
end


lemma Trigo_5_353_DGDW_extend(h0 : cos(x/2) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (2*cos(x+122*pi))≠ 0) (h3 : cos((x)/2)≠ 0) (h4 : sin(x)≠ 0) (h5 : cos(-x+21*pi/2)≠ 0) : ((1 - cos(x))*tan(x)/cos(-x + 21*pi/2) + 1)*sin(2*x)/(2*cos(x + 122*pi))=tan(x):=
begin
have : sin(x) = cos(-x + 21*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (x) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((1 - cos(x)) / sin(x) * tan(x) + 1) * sin(2 * x) / (2 * cos(x + 122 * pi)) = ((1 - cos(x))*tan(x)/sin(x) + 1)*sin(2*x)/(2*cos(x + 122*pi)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(x/2) = ( 1 - cos(x) ) / sin(x),
{
have : tan(x/2) = tan((x)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : cos(x) = cos(x + 122*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (x) (61),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw tan_eq_sin_div_cos,
have : sin(x/2)/cos(x/2)*(sin(x)/cos(x)) + 1 = (sin(x/2)*sin(x) + cos(x/2)*cos(x))/(cos(x/2)*cos(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : sin(x/2)*sin(x) + cos(x/2)*cos(x) = cos(x/2),
{
rw add_comm,
rw ← cos_sub,
rw ← cos_neg (x/2),
apply congr_arg,
ring,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_354_GNBL_extend : 2*(4*cos(25*pi/18)**3 - 3*cos(25*pi/18))*sin(209*pi/6)*cos(209*pi/6)*tan(5*pi/4)=-3/4:=
begin
have : (4 * cos(25 * pi / 18) ** 3 - 3 * cos(25 * pi / 18)) * (2 * sin(209 * pi / 6) * cos(209 * pi / 6)) * tan(5 * pi / 4) = 2*(4*cos(25*pi/18)**3 - 3*cos(25*pi/18))*sin(209*pi/6)*cos(209*pi/6)*tan(5*pi/4),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(209*pi/3) = 2 * sin(209*pi/6) * cos(209*pi/6),
{
have : sin(209*pi/3) = sin(2*(209*pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/3) = sin(209*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4*pi/3) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 3) * (4 * cos(25 * pi / 18) ** 3 - 3 * cos(25 * pi / 18)) * tan(5 * pi / 4) = (4*cos(25*pi/18)**3 - 3*cos(25*pi/18))*sin(4*pi/3)*tan(5*pi/4),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(25*pi/6) = 4 * cos(25*pi/18) ** 3 - 3 * cos(25*pi/18),
{
have : cos(25*pi/6) = cos(3*(25*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/3) = -sin(pi/3),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(25*pi/6) = cos(pi/6),
{
rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(5*pi/4) = tan(pi/4),
{
rw tan_eq_tan_add_int_mul_pi (5*pi/4) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_three,
rw cos_pi_div_six,
rw tan_pi_div_four,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_5_355_QVHL_extend(h0 : cos(pi/18) ≠ 0) (h1 : sin(4*pi/9) ≠ 0)  (h2 : tan(824*pi/9)≠ 0) : (-2*sqrt(3)/tan(824*pi/9) + 2)*(cos(pi/2)*cos(13*pi/18) + sin(pi/2)*sin(2921*pi/18))=2:=
begin
have : ((-2) * sqrt 3 / tan(824 * pi / 9) + 2) * (cos(pi / 2) * cos(13 * pi / 18) + sin(pi / 2) * sin(2921 * pi / 18)) = (-2*sqrt(3)/tan(824*pi/9) + 2)*(cos(pi/2)*cos(13*pi/18) + sin(pi/2)*sin(2921*pi/18)),
{
field_simp at *,
},
have : sin(13*pi/18) = sin(2921*pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (13*pi/18) (81),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-2) * sqrt 3 / tan(824 * pi / 9) + 2) * (sin(13 * pi / 18) * sin(pi / 2) + cos(13 * pi / 18) * cos(pi / 2)) = (-2*sqrt(3)/tan(824*pi/9) + 2)*(cos(pi/2)*cos(13*pi/18) + sin(pi/2)*sin(13*pi/18)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = sin(13*pi/18) * sin(pi/2) + cos(13*pi/18) * cos(pi/2),
{
have : cos(2*pi/9) = cos((13*pi/18) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * (sqrt 3 * ((-1) / tan(824 * pi / 9)) + 1) * cos(2 * pi / 9) = (-2*sqrt(3)/tan(824*pi/9) + 2)*cos(2*pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = -1 / tan(824*pi/9),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/18) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sqrt(3)*(sin(pi/18)/cos(pi/18)) + 1 = (sqrt(3)*sin(pi/18) + cos(pi/18))/cos(pi/18),
{
ring_exp,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sqrt(3)*sin(pi/18) = 2*cos(pi/6)*sin(pi/18),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
rw mul_right_comm 2 (cos(pi/6)) (sin(pi/18)),
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
have : 2*(2*sin(2*pi/9)/(2*sin(pi/6)*cos(pi/18)))*cos(2*pi/9) = 2*2*(sin(2*pi/9)*cos(2*pi/9)/(2*sin(pi/6)*cos(pi/18))),
{
ring,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(pi/18) = sin(4*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_5_356_KJSS_extend(h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/10) ≠ 0)  (h2 : tan(227*pi/5)≠ 0) (h3 : (sqrt(3)*(1/tan(227*pi/5))+1)≠ 0) (h4 : (sqrt(3)/tan(227*pi/5)+1)≠ 0) (h5 : (sqrt(3)*cos(227*pi/5)/sin(227*pi/5)+1)≠ 0) (h6 : sin(227*pi/5)≠ 0) (h7 : cos(227*pi/5)≠ 0) (h8 : (sqrt(3)/(sin(227*pi/5)/cos(227*pi/5))+1)≠ 0) (h9 : (sin(227*pi/5)/cos(227*pi/5))≠ 0) (h10 : cos(451*pi/10)≠ 0) (h11 : (sqrt(3)*cos(227*pi/5)/cos(451*pi/10)+1)≠ 0) : (-cos(227*pi/5)/cos(451*pi/10) + sqrt(3))/(sqrt(3)*cos(227*pi/5)/cos(451*pi/10) + 1)=tan(7*pi/30):=
begin
have : (-cos(227 * pi / 5) / cos(451 * pi / 10) + sqrt 3) / (sqrt 3 * cos(227 * pi / 5) / cos(451 * pi / 10) + 1) = (-cos(227*pi/5)/cos(451*pi/10) + sqrt(3))/(sqrt(3)*cos(227*pi/5)/cos(451*pi/10) + 1),
{
field_simp at *,
},
have : sin(227*pi/5) = cos(451*pi/10),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (227*pi/5) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-1) / (sin(227 * pi / 5) / cos(227 * pi / 5)) + sqrt 3) / (sqrt 3 / (sin(227 * pi / 5) / cos(227 * pi / 5)) + 1) = (-cos(227*pi/5)/sin(227*pi/5) + sqrt(3))/(sqrt(3)*cos(227*pi/5)/sin(227*pi/5) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(227*pi/5) = sin(227*pi/5) / cos(227*pi/5),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (-(1 / tan(227 * pi / 5)) + sqrt 3) / (sqrt 3 * (1 / tan(227 * pi / 5)) + 1) = (-1/tan(227*pi/5) + sqrt(3))/(sqrt(3)/tan(227*pi/5) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) = 1 / tan(227*pi/5),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/10) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3) = tan(pi/3),
{
field_simp,
},
rw this,
rw mul_comm,
have : (-tan(pi/10) + tan(pi/3))/(tan(pi/10)*tan(pi/3) + 1) = tan(7*pi/30),
{
have : tan(7*pi/30) = tan((pi/3) - (pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
field_simp,
ring_exp,
repeat {assumption},
},
rw this,
end


lemma Trigo_5_357_SLFQ_extend(h0 : sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : sin(pi/9) ≠ 0) (h3 : (sin(5*pi/9)*cos(pi/2)-sin(pi/2)*cos(5*pi/9))≠ 0) (h4 : cos(pi/18)≠ 0) (h5 : (sin(5*pi/9)*cos(pi/2)- -cos(149*pi)*cos(5*pi/9))≠ 0) (h6 : (sin(5*pi/9)*cos(pi/2)+cos(5*pi/9)*cos(149*pi))≠ 0) (h7 : ((-4*sin(5*pi/27)**3+3*sin(5*pi/27))*cos(pi/2)+cos(5*pi/9)*cos(149*pi))≠ 0) (h8 : (((-4)*sin(5*pi/27)**3+3*sin(5*pi/27))*cos(pi/2)+cos(5*pi/9)*cos(149*pi))≠ 0) : -sqrt(3)/cos(pi/18) + 1/((-4*sin(5*pi/27)**3 + 3*sin(5*pi/27))*cos(pi/2) + cos(5*pi/9)*cos(149*pi))=4:=
begin
have : -sqrt 3 / cos(pi / 18) + 1 / (((-4) * sin(5 * pi / 27) ** 3 + 3 * sin(5 * pi / 27)) * cos(pi / 2) + cos(5 * pi / 9) * cos(149 * pi)) = -sqrt(3)/cos(pi/18) + 1/((-4*sin(5*pi/27)**3 + 3*sin(5*pi/27))*cos(pi/2) + cos(5*pi/9)*cos(149*pi)),
{
field_simp at *,
},
have : sin(5*pi/9) = -4 * sin(5*pi/27) ** 3 + 3 * sin(5*pi/27),
{
have : sin(5*pi/9) = sin(3*(5*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 / cos(pi / 18) + 1 / (sin(5 * pi / 9) * cos(pi / 2) - -cos(149 * pi) * cos(5 * pi / 9)) = -sqrt(3)/cos(pi/18) + 1/(sin(5*pi/9)*cos(pi/2) + cos(5*pi/9)*cos(149*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/2) = -cos(149*pi),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/2) (74),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 / cos(pi / 18) + 1 / (sin(5 * pi / 9) * cos(pi / 2) - sin(pi / 2) * cos(5 * pi / 9)) = -sqrt(3)/cos(pi/18) + 1/(sin(5*pi/9)*cos(pi/2) - sin(pi/2)*cos(5*pi/9)),
{
field_simp at *,
},
have : sin(pi/18) = sin(5*pi/9) * cos(pi/2) - sin(pi/2) * cos(5*pi/9),
{
have : sin(pi/18) = sin((5*pi/9) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt(3)/cos(pi/18) + 1/sin(pi/18) = (-sqrt(3)*sin(pi/18) + cos(pi/18))/(sin(pi/18)*cos(pi/18)),
{
ring_exp,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
left,
ring_exp,
},
rw this,
have : -sqrt(3)*sin(pi/18) = -2*sin(pi/18)*sin(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*cos(pi/18)*cos(pi/3),
{
field_simp,
ring_exp,
},
rw this,
have : -2*sin(pi/18)*sin(pi/3) + 2*cos(pi/18)*cos(pi/3) = 2*cos(7*pi/18),
{
have : cos(7*pi/18) = -sin(pi/18)*sin(pi/3) + cos(pi/18)*cos(pi/3),
{
have : cos(7*pi/18) = cos((pi/3) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
linarith,
},
rw this,
have : cos(7*pi/18) = sin(pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_assoc,
have : cos(pi/18)*cos(pi/3) = cos(pi/18)/2,
{
field_simp,
},
rw this,
have : sin(pi/18)*(2*(cos(pi/18)/2)) = sin(pi/18)*cos(pi/18),
{
ring,
},
rw this,
have : sin(pi/18)*cos(pi/18) = sin(pi/9)/2,
{
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_358_OIJT_extend(h0 : sin(x) + cos(x) + 1 ≠ 0)  (h1 : sin(x)≠ 0) (h2 : (sin(x)+1+sin(2*x)/(2*sin(x)))≠ 0) (h3 : (2*sin(x))≠ 0) (h4 : (sin(x)+sin(2*x)/(2*sin(x))+1)≠ 0) (h5 : (sin(x)+1+cos(-2*x+145*pi/2)/(2*sin(x)))≠ 0) (h6 : (sin(x)+1+cos((-2)*x+145*pi/2)/(2*sin(x)))≠ 0) (h7 : (sin(x)+1+(sin((-2)*x+141*pi/2)*sin((-2)*pi)+cos((-2)*x+141*pi/2)*cos((-2)*pi))/(2*sin(x)))≠ 0) (h8 : ((sin(-2*pi)*sin(-2*x+141*pi/2)+cos(-2*pi)*cos(-2*x+141*pi/2))/(2*sin(x))+sin(x)+1)≠ 0) : -sqrt(2)*sin(x + pi/4) + ((sin(-2*pi)*sin(-2*x + 141*pi/2) + cos(-2*pi)*cos(-2*x + 141*pi/2))/(2*sin(x)) + sin(x) + sin(-2*pi)*sin(-2*x + 141*pi/2) + cos(-2*pi)*cos(-2*x + 141*pi/2) + 1)/((sin(-2*pi)*sin(-2*x + 141*pi/2) + cos(-2*pi)*cos(-2*x + 141*pi/2))/(2*sin(x)) + sin(x) + 1)=0:=
begin
have : -sqrt 2 * sin(x + pi / 4) + (sin(x) + (sin((-2) * x + 141 * pi / 2) * sin((-2) * pi) + cos((-2) * x + 141 * pi / 2) * cos((-2) * pi)) + 1 + (sin((-2) * x + 141 * pi / 2) * sin((-2) * pi) + cos((-2) * x + 141 * pi / 2) * cos((-2) * pi)) / (2 * sin(x))) / (sin(x) + 1 + (sin((-2) * x + 141 * pi / 2) * sin((-2) * pi) + cos((-2) * x + 141 * pi / 2) * cos((-2) * pi)) / (2 * sin(x))) = -sqrt(2)*sin(x + pi/4) + ((sin(-2*pi)*sin(-2*x + 141*pi/2) + cos(-2*pi)*cos(-2*x + 141*pi/2))/(2*sin(x)) + sin(x) + sin(-2*pi)*sin(-2*x + 141*pi/2) + cos(-2*pi)*cos(-2*x + 141*pi/2) + 1)/((sin(-2*pi)*sin(-2*x + 141*pi/2) + cos(-2*pi)*cos(-2*x + 141*pi/2))/(2*sin(x)) + sin(x) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*x + 145*pi/2) = sin(-2*x + 141*pi/2) * sin(-2*pi) + cos(-2*x + 141*pi/2) * cos(-2*pi),
{
have : cos(-2*x + 145*pi/2) = cos((-2*x + 141*pi/2) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 2 * sin(x + pi / 4) + (sin(x) + cos((-2) * x + 145 * pi / 2) + 1 + cos((-2) * x + 145 * pi / 2) / (2 * sin(x))) / (sin(x) + 1 + cos((-2) * x + 145 * pi / 2) / (2 * sin(x))) = -sqrt(2)*sin(x + pi/4) + (sin(x) + cos(-2*x + 145*pi/2) + 1 + cos(-2*x + 145*pi/2)/(2*sin(x)))/(sin(x) + 1 + cos(-2*x + 145*pi/2)/(2*sin(x))),
{
field_simp at *,
},
have : sin(2*x) = cos(-2*x + 145*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*x) (36),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(x) + sin(2 * x) + sin(2 * x) / (2 * sin(x)) + 1) / (sin(x) + sin(2 * x) / (2 * sin(x)) + 1) - sqrt 2 * sin(x + pi / 4) = -sqrt(2)*sin(x + pi/4) + (sin(x) + sin(2*x) + 1 + sin(2*x)/(2*sin(x)))/(sin(x) + 1 + sin(2*x)/(2*sin(x))),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(2*x) / ( 2 * sin(x) ),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi/4) = sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(x+pi/4) = sin((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
have : sqrt(2)*(sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x)) = sin(x) + cos(x),
{
ring_exp,
rw sq_sqrt,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
linarith,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
have : sin(x) + 2*sin(x)*cos(x) + cos(x) + 1 = sin(x) + 2*sin(x)*cos(x) + cos(x) + (sin(x)**2 + cos(x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(x) + 2*sin(x)*cos(x) + cos(x) + (sin(x)**2 + cos(x)**2) = 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2 + sin(x) + cos(x),
{
ring,
},
rw this,
have : 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2 = (sin(x) + cos(x))**2,
{
ring_exp,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_359_PLXD_extend(h0 : cos(y) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : 1 - tan(x) * tan(y) ≠ 0) (h3 : tan(x) ≠ 0) (h4: tan(x + y) ≠ 0)  (h5 : tan(-x-y+59*pi/2)≠ 0) (h6 : tan(x)≠ 0) (h7 : (tan(x)*(1/tan(-x-y+59*pi/2)))≠ 0) (h8 : cos((2*y)/2)≠ 0) (h9 : (cos(2*y)+1)≠ 0) (h10 : (1+cos(2*y))≠ 0) (h11 : (1/tan(-x+143*pi/2))≠ 0) (h12 : tan(-x+143*pi/2)≠ 0) : (1/tan(-x - y + 59*pi/2) - 1/tan(-x + 143*pi/2) - sin(2*y)/(cos(2*y) + 1))*tan(-x + 143*pi/2)*tan(-x - y + 59*pi/2)=tan(y):=
begin
have : (-(1 / tan(-x + 143 * pi / 2)) + 1 / tan(-x - y + 59 * pi / 2) - sin(2 * y) / (cos(2 * y) + 1)) * tan(-x - y + 59 * pi / 2) / (1 / tan(-x + 143 * pi / 2)) = (1/tan(-x - y + 59*pi/2) - 1/tan(-x + 143*pi/2) - sin(2*y)/(cos(2*y) + 1))*tan(-x + 143*pi/2)*tan(-x - y + 59*pi/2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x) = 1 / tan(-x + 143*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (x) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-tan(x) - sin(2 * y) / (1 + cos(2 * y)) + 1 / tan(-x - y + 59 * pi / 2)) * tan(-x - y + 59 * pi / 2) / tan(x) = (-tan(x) + 1/tan(-x - y + 59*pi/2) - sin(2*y)/(cos(2*y) + 1))*tan(-x - y + 59*pi/2)/tan(x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(y) = sin(2*y) / ( 1 + cos(2*y) ),
{
have : tan(y) = tan((2*y)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-tan(x) - tan(y) + 1 / tan(-x - y + 59 * pi / 2)) / (tan(x) * (1 / tan(-x - y + 59 * pi / 2))) = (-tan(x) - tan(y) + 1/tan(-x - y + 59*pi/2))*tan(-x - y + 59*pi/2)/tan(x),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(x + y) = 1 / tan(-x - y + 59*pi/2),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (x + y) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -tan(x) - tan(y) = -tan(x + y)*(-tan(x)*tan(y) + 1),
{
have : tan(x) + tan(y) = (-tan(x)*tan(y) + 1)*tan(x + y),
{
rw tan_add_tan,
have : tan((x) + (y)) = tan(x + y),
{
apply congr_arg,
ring,
},
ring,
repeat {assumption},
},
linarith,
},
rw this,
have : -tan(x + y)*(-tan(x)*tan(y) + 1) + tan(x + y) = tan(x)*tan(y)*tan(x + y),
{
ring_exp,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_360_XQHO_extend(h0 : sin(pi/9) ≠ 0)  : -(-1 + 2*sin(pi/18)**2)*sin(17*pi/18)*cos(610*pi/9)=1/8:=
begin
have : -(1 - 2 * sin(pi / 18) ** 2) * sin(17 * pi / 18) * -cos(610 * pi / 9) = -(-1 + 2*sin(pi/18)**2)*sin(17*pi/18)*cos(610*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(247*pi/18) = -cos(610*pi/9),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (247*pi/18) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - 2 * sin(pi / 18) ** 2) * -sin(247 * pi / 18) * sin(17 * pi / 18) = -(1 - 2*sin(pi/18)**2)*sin(17*pi/18)*sin(247*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = -sin(247*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/18) (7),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5 * pi / 18) * sin(17 * pi / 18) * (1 - 2 * sin(pi / 18) ** 2) = (1 - 2*sin(pi/18)**2)*sin(5*pi/18)*sin(17*pi/18),
{
field_simp at *,
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
have : sin(5*pi/18) = cos(2*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(17*pi/18) = cos(4*pi/9),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (17*pi/18) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : cos(2*pi/9)*cos(4*pi/9)*(sin(2*pi/9)/(2*sin(pi/9))) = sin(2*pi/9)*cos(2*pi/9)*cos(4*pi/9)/(2*sin(pi/9)),
{
ring,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/9)/2*cos(4*pi/9) = sin(4*pi/9)*cos(4*pi/9)/2,
{
ring,
},
rw this,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_361_KOPV_extend(h0 : sin(pi/18) ≥ 0) (h1 : -cos(pi/18) + sin(pi/18) ≤ 0) (h2 : -sin(pi/18) + cos(pi/18) ≠ 0)  (h3 : (-sqrt(1-cos(2393*pi/18)**2)+cos(35*pi/18))≠ 0) (h4 : (-sqrt(1-(-sin(2375*pi/18)*sin(pi)+cos(2375*pi/18)*cos(pi))**2)+cos(35*pi/18))≠ 0) (h5 : (-sqrt(1-(cos(pi)*cos(2375*pi/18)-sin(pi)*sin(2375*pi/18))**2)+cos(35*pi/18))≠ 0) (h6 : (-sqrt(1-(cos(2357*pi/18)/2+cos(2393*pi/18)/2-sin(pi)*sin(2375*pi/18))**2)+cos(35*pi/18))≠ 0) : sqrt(1 - sin(pi/9))/(-sqrt(1 - (cos(2357*pi/18)/2 + cos(2393*pi/18)/2 - sin(pi)*sin(2375*pi/18))**2) + cos(35*pi/18))=1:=
begin
have : cos(2375*pi/18) * cos(pi) = cos(2357*pi/18) / 2 + cos(2393*pi/18) / 2,
{
rw cos_mul_cos,
have : cos((2375*pi/18) + (pi)) = cos(2393*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2375*pi/18) - (pi)) = cos(2357*pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(2375*pi/18) * cos(pi)) = cos(pi)*cos(2375*pi/18),
{
ring,
},
conv {to_lhs, rw this,},
have : sqrt (1 - sin(pi / 9)) / (-sqrt (1 - (-sin(2375 * pi / 18) * sin(pi) + cos(2375 * pi / 18) * cos(pi)) ** 2) + cos(35 * pi / 18)) = sqrt(1 - sin(pi/9))/(-sqrt(1 - (cos(pi)*cos(2375*pi/18) - sin(pi)*sin(2375*pi/18))**2) + cos(35*pi/18)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2393*pi/18) = -sin(2375*pi/18) * sin(pi) + cos(2375*pi/18) * cos(pi),
{
have : cos(2393*pi/18) = cos((2375*pi/18) + (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/18) = cos(2393*pi/18),
{
rw cos_eq_cos_add_int_mul_two_pi (17*pi/18) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw ← sin_sq,
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : 1 - 2*sin(pi/18)*cos(pi/18) = sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(pi/18)*cos(pi/18),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(pi/18)*cos(pi/18) = (-cos(pi/18) + sin(pi/18))**2,
{
ring_exp,
},
rw this,
have : sin(17*pi/18) = sin(pi/18),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(35*pi/18) = cos(pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (35*pi/18) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
repeat {rw sqrt_sq_eq_abs},
rw abs_eq_self.mpr h0,
rw abs_eq_neg_self.mpr h1,
norm_num,
field_simp,
end


lemma Trigo_5_362_MKTN_extend(h0 : 1 - tan(pi/10) * tan(7*pi/30) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : cos(7*pi/30) ≠ 0) (h3 : tan(pi/10) ≠ 0) (h4 : tan(7*pi/30) ≠ 0) (h5 : sqrt(3) ≠ 0)  (h6 : cos((pi/5)/2)≠ 0) (h7 : (cos(pi/5)+1)≠ 0) (h8 : (sin(pi/5)/(1+cos(pi/5))*tan(7*pi/30)*tan(pi/3))≠ 0) (h9 : (1+cos(pi/5))≠ 0) (h10 : (sin(pi/5)*tan(7*pi/30)*tan(pi/3))≠ 0) (h11 : (2*cos(pi/10)**2-1+1)≠ 0) (h12 : (2*cos(pi/10)**2)≠ 0) (h13 : (sin(pi/5)*tan(7*pi/30)*tan(41*pi/3))≠ 0) (h14 : cos(pi/10)≠ 0) (h15 : (sin(pi/5)*tan(7*pi/30)*-tan(41*pi/3))≠ 0) : -(2*tan(2*pi/3) + sin(pi/5)/cos(pi/10)**2 + 2*tan(7*pi/30))*cos(pi/10)**2/(sin(pi/5)*tan(7*pi/30)*tan(41*pi/3))=-1:=
begin
have : 2 * (tan(2 * pi / 3) + sin(pi / 5) / (2 * cos(pi / 10) ** 2) + tan(7 * pi / 30)) * cos(pi / 10) ** 2 / (sin(pi / 5) * tan(7 * pi / 30) * -tan(41 * pi / 3)) = -(2*tan(2*pi/3) + sin(pi/5)/cos(pi/10)**2 + 2*tan(7*pi/30))*cos(pi/10)**2/(sin(pi/5)*tan(7*pi/30)*tan(41*pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/3) = -tan(41*pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/3) (14),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * cos(pi / 10) ** 2 - 1 + 1) * (tan(2 * pi / 3) + sin(pi / 5) / (2 * cos(pi / 10) ** 2 - 1 + 1) + tan(7 * pi / 30)) / (sin(pi / 5) * tan(7 * pi / 30) * tan(pi / 3)) = 2*(tan(2*pi/3) + sin(pi/5)/(2*cos(pi/10)**2) + tan(7*pi/30))*cos(pi/10)**2/(sin(pi/5)*tan(7*pi/30)*tan(pi/3)),
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
have : (sin(pi / 5) / (1 + cos(pi / 5)) + tan(7 * pi / 30) + tan(2 * pi / 3)) / (sin(pi / 5) / (1 + cos(pi / 5)) * tan(7 * pi / 30) * tan(pi / 3)) = (cos(pi/5) + 1)*(tan(2*pi/3) + sin(pi/5)/(cos(pi/5) + 1) + tan(7*pi/30))/(sin(pi/5)*tan(7*pi/30)*tan(pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) = sin(pi/5) / ( 1 + cos(pi/5) ),
{
have : tan(pi/10) = tan((pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(pi/10) + tan(7*pi/30) = (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/10) + (7*pi/30)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3) = -tan(pi/10)*tan(7*pi/30)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
field_simp,
end


lemma Trigo_5_363_KGWA_extend(h0 : -cos(pi/18) + sin(pi/18) ≠ 0) (h1 : -sin(pi/18) + cos(pi/18) ≥ 0) (h2 : cos(pi/18) ≥ 0)  (h3 : (-sqrt(1-sin(pi/18)**2)+sin(pi/18))≠ 0) (h4 : (-sqrt(1-(-4*sin(pi/54)**3+3*sin(pi/54))**2)-4*sin(pi/54)**3+3*sin(pi/54))≠ 0) (h5 : (-sqrt(1-((-4)*sin(pi/54)**3+3*sin(pi/54))**2)+((-4)*sin(pi/54)**3+3*sin(pi/54)))≠ 0) : sqrt(-2*(-4*sin(pi/54)**3 + 3*sin(pi/54))*sin(2848*pi/9) + 1)/(-sqrt(1 - (-4*sin(pi/54)**3 + 3*sin(pi/54))**2) - 4*sin(pi/54)**3 + 3*sin(pi/54))=-1:=
begin
have : sqrt ((-2) * ((-4) * sin(pi / 54) ** 3 + 3 * sin(pi / 54)) * sin(2848 * pi / 9) + 1) / (-sqrt (1 - ((-4) * sin(pi / 54) ** 3 + 3 * sin(pi / 54)) ** 2) + ((-4) * sin(pi / 54) ** 3 + 3 * sin(pi / 54))) = sqrt(-2*(-4*sin(pi/54)**3 + 3*sin(pi/54))*sin(2848*pi/9) + 1)/(-sqrt(1 - (-4*sin(pi/54)**3 + 3*sin(pi/54))**2) - 4*sin(pi/54)**3 + 3*sin(pi/54)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = -4 * sin(pi/54) ** 3 + 3 * sin(pi/54),
{
have : sin(pi/18) = sin(3*(pi/54)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * sin(2848 * pi / 9) + 1) / (-sqrt (1 - sin(pi / 18) ** 2) + sin(pi / 18)) = sqrt(-2*sin(pi/18)*sin(2848*pi/9) + 1)/(-sqrt(1 - sin(pi/18)**2) + sin(pi/18)),
{
field_simp at *,
},
have : cos(3203*pi/18) = sin(2848*pi/9),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (3203*pi/18) (69),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt ((-2) * sin(pi / 18) * cos(3203 * pi / 18) + 1) / (-sqrt (1 - sin(pi / 18) ** 2) + sin(pi / 18)) = sqrt(-2*sin(pi/18)*cos(3203*pi/18) + 1)/(-sqrt(1 - sin(pi/18)**2) + sin(pi/18)),
{
field_simp at *,
},
have : cos(pi/18) = cos(3203*pi/18),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/18) (89),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -2*sin(pi/18)*cos(pi/18) + 1 = -2*sin(pi/18)*cos(pi/18) + (sin(pi/18)**2 + cos(pi/18)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : -2*sin(pi/18)*cos(pi/18) + (sin(pi/18)**2 + cos(pi/18)**2) = (-sin(pi/18) + cos(pi/18))**2,
{
ring_exp,
},
rw this,
rw ← cos_sq',
repeat {rw sqrt_sq_eq_abs},
rw abs_eq_self.mpr h1,
rw abs_eq_self.mpr h2,
field_simp,
end


lemma Trigo_5_364_FKRF_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (sin(-x-pi)*cos(-x-pi))≠ 0) : (sin(-2*pi)*sin(-x) + cos(-2*pi)*cos(-x))*(-4*sin(-x/3 + 25*pi/2)**3 + 3*sin(-x/3 + 25*pi/2))*tan(pi - x)/(sin(-x - pi)*cos(-x - pi))=-1:=
begin
have : ((-4) * sin(-x / 3 + 25 * pi / 2) ** 3 + 3 * sin(-x / 3 + 25 * pi / 2)) * (sin(-x) * sin((-2) * pi) + cos(-x) * cos((-2) * pi)) * tan(pi - x) / (sin(-x - pi) * cos(-x - pi)) = (sin(-2*pi)*sin(-x) + cos(-2*pi)*cos(-x))*(-4*sin(-x/3 + 25*pi/2)**3 + 3*sin(-x/3 + 25*pi/2))*tan(pi - x)/(sin(-x - pi)*cos(-x - pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = sin(-x) * sin(-2*pi) + cos(-x) * cos(-2*pi),
{
have : cos(-x + 2*pi) = cos((-x) - (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(-x / 3 + 25 * pi / 2) ** 3 + 3 * sin(-x / 3 + 25 * pi / 2)) * cos(-x + 2 * pi) * tan(pi - x) / (sin(-x - pi) * cos(-x - pi)) = (-4*sin(-x/3 + 25*pi/2)**3 + 3*sin(-x/3 + 25*pi/2))*cos(-x + 2*pi)*tan(pi - x)/(sin(-x - pi)*cos(-x - pi)),
{
field_simp at *,
},
have : sin(-x + 75*pi/2) = -4 * sin(-x/3 + 25*pi/2) ** 3 + 3 * sin(-x/3 + 25*pi/2),
{
have : sin(-x + 75*pi/2) = sin(3*(-x/3 + 25*pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 3*pi/2) = sin(-x + 75*pi/2),
{
rw sin_eq_sin_add_int_mul_two_pi (-x + 3*pi/2) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x + 3*pi/2) = -cos(x),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 3*pi/2) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(pi - x) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi - x) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(-x - pi) = -cos(x),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
field_simp,
ring_exp,
end


lemma Trigo_5_365_BJJC_extend(h0 : sin(x) ≠ 0) (h1 : tan(x) ≠ 0)  (h2 : (sin(-x-pi)*tan(-x-pi))≠ 0) (h3 : (cos(x+283*pi/2)*tan(-x-pi))≠ 0) (h4 : (sin(-x-141*pi)*tan(-x-pi))≠ 0) : (-sin(-pi/6)*sin(-x + 11*pi/6) - cos(-pi/6)*cos(-x + 11*pi/6))*sin(pi - x)*tan(pi - x)/(sin(-x - 141*pi)*tan(-x - pi))=-cos(x):=
begin
have : cos(x + 283*pi/2) = sin(-x - 141*pi),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (x + 283*pi/2) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(-pi / 6) * sin(-x + 11 * pi / 6) + cos(-pi / 6) * cos(-x + 11 * pi / 6)) * sin(pi - x) * tan(pi - x) / (cos(x + 283 * pi / 2) * tan(-x - pi)) = (-sin(-pi/6)*sin(-x + 11*pi/6) - cos(-pi/6)*cos(-x + 11*pi/6))*sin(pi - x)*tan(pi - x)/(cos(x + 283*pi/2)*tan(-x - pi)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-x - pi) = cos(x + 283*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x - pi) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi - x) * (sin(-x + 11 * pi / 6) * sin(-pi / 6) + cos(-x + 11 * pi / 6) * cos(-pi / 6)) * tan(pi - x) / (sin(-x - pi) * tan(-x - pi)) = -(sin(-pi/6)*sin(-x + 11*pi/6) + cos(-pi/6)*cos(-x + 11*pi/6))*sin(pi - x)*tan(pi - x)/(sin(-x - pi)*tan(-x - pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 2*pi) = sin(-x + 11*pi/6) * sin(-pi/6) + cos(-x + 11*pi/6) * cos(-pi/6),
{
have : cos(-x + 2*pi) = cos((-x + 11*pi/6) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi - x) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(-x + 2*pi) = cos(x),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : tan(pi - x) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi - x) (1),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x - pi) = sin(x),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(-x - pi) = -tan(x),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (-1),
repeat {apply congr_arg _},
simp,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_366_SYGI_extend(h0 : sin(pi/9) ≠ 0)  (h1 : (sin(pi/18)*-cos(125*pi/18))≠ 0) (h2 : (sin(pi/18)*cos(125*pi/18))≠ 0) (h3 : (sin(pi/18)*(-sin(125*pi/36)**2+cos(125*pi/36)**2))≠ 0) (h4 : ((-sin(125*pi/36)**2+cos(125*pi/36)**2)*sin(pi/18))≠ 0) (h5 : ((-sin(125*pi/36)**2+cos(-125*pi/36)**2)*sin(pi/18))≠ 0) (h6 : ((-sin(125*pi/36)**2+cos((-125)*pi/36)**2)*sin(pi/18))≠ 0) : (1/2 - sin(7*pi/36)**2)/((-sin(125*pi/36)**2 + cos(-125*pi/36)**2)*sin(pi/18))=-1:=
begin
have : (1 / 2 - sin(7 * pi / 36) ** 2) / ((-sin(125 * pi / 36) ** 2 + cos((-125) * pi / 36) ** 2) * sin(pi / 18)) = (1/2 - sin(7*pi/36)**2)/((-sin(125*pi/36)**2 + cos(-125*pi/36)**2)*sin(pi/18)),
{
field_simp at *,
},
have : cos(125*pi/36) = cos(-125*pi/36),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (125*pi/36) (0),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -((-1) / 2 + sin(7 * pi / 36) ** 2) / (sin(pi / 18) * (-sin(125 * pi / 36) ** 2 + cos(125 * pi / 36) ** 2)) = (1/2 - sin(7*pi/36)**2)/((-sin(125*pi/36)**2 + cos(125*pi/36)**2)*sin(pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(125*pi/18) = -sin(125*pi/36) ** 2 + cos(125*pi/36) ** 2,
{
have : cos(125*pi/18) = cos(2*(125*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(7 * pi / 36) ** 2 - 1 / 2) / (sin(pi / 18) * -cos(125 * pi / 18)) = -(-1/2 + sin(7*pi/36)**2)/(sin(pi/18)*cos(125*pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = -cos(125*pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi/18) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/36)**2 = 1/2 - cos(7*pi/18)/2,
{
have : cos(7*pi/18) = cos(2*(7*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : sin(pi/18)*cos(pi/18) = sin(pi/9)/2,
{
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(7*pi/18) = sin(pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_5_367_SYMU_extend(h0 : 2 ≠ 0)  : (1 - 2*cos(x/2 + pi/12)**2)*sin(x - pi/6) + (-sin(pi/3)*sin(-x + 35*pi/6) + cos(pi/3)*cos(-x + 35*pi/6))*sin(x + pi/6)=sqrt(3)/2:=
begin
have : (1 - 2 * cos(x / 2 + pi / 12) ** 2) * sin(x - pi / 6) + sin(x + pi / 6) * (-sin(-x + 35 * pi / 6) * sin(pi / 3) + cos(-x + 35 * pi / 6) * cos(pi / 3)) = (1 - 2*cos(x/2 + pi/12)**2)*sin(x - pi/6) + (-sin(pi/3)*sin(-x + 35*pi/6) + cos(pi/3)*cos(-x + 35*pi/6))*sin(x + pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 37*pi/6) = -sin(-x + 35*pi/6) * sin(pi/3) + cos(-x + 35*pi/6) * cos(pi/3),
{
have : cos(-x + 37*pi/6) = cos((-x + 35*pi/6) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : -(2 * cos(x / 2 + pi / 12) ** 2 - 1) * sin(x - pi / 6) + sin(x + pi / 6) * cos(-x + 37 * pi / 6) = (1 - 2*cos(x/2 + pi/12)**2)*sin(x - pi/6) + sin(x + pi/6)*cos(-x + 37*pi/6),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x - pi/6) = cos(-x + 37*pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x - pi/6) (3),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x - pi / 6) * (2 * cos(x / 2 + pi / 12) ** 2 - 1) + sin(x + pi / 6) * cos(x - pi / 6) = -(2*cos(x/2 + pi/12)**2 - 1)*sin(x - pi/6) + sin(x + pi/6)*cos(x - pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi/6) = 2 * cos(x/2 + pi/12) ** 2 - 1,
{
have : cos(x + pi/6) = cos(2*(x/2 + pi/12)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : -sin(x - pi/6) = -sin(x)*cos(pi/6) + sin(pi/6)*cos(x),
{
have : sin(x - pi/6) = -sin(pi/6)*cos(x) + sin(x)*cos(pi/6),
{
have : sin(x - pi/6) = sin((x) - (pi/6)),
{
apply congr_arg,
ring,
},
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : cos(x + pi/6) = -sin(pi/6)*sin(x) + cos(pi/6)*cos(x),
{
have : cos(x+pi/6) = cos((x) + (pi/6)),
{
apply congr_arg,
ring,
},
rw cos_add,
ring,
},
rw this,
have : sin(x + pi/6) = sin(x)*cos(pi/6) + sin(pi/6)*cos(x),
{
have : sin(x+pi/6) = sin((x) + (pi/6)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
rw this,
have : cos(x - pi/6) = sin(pi/6)*sin(x) + cos(pi/6)*cos(x),
{
have : cos(x-pi/6) = cos((x) - (pi/6)),
{
apply congr_arg,
ring,
},
rw cos_sub,
ring,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
have : (-sin(x)*(sqrt(3)/2) + 1/2*cos(x))*(-(1/2)*sin(x) + sqrt(3)/2*cos(x)) + (sin(x)*(sqrt(3)/2) + 1/2*cos(x))*(1/2*sin(x) + sqrt(3)/2*cos(x)) = sqrt(3)*(sin(x)**2 + cos(x)**2)/2,
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
end


lemma Trigo_5_368_BLFE_extend(h0 : -sin(x) + cos(x) ≠ 0)  (h1 : sin(-x+pi/4)≠ 0) : -(-sin(pi/6)*sin(-2*x + 1733*pi/6) + cos(pi/6)*cos(-2*x + 1733*pi/6))/sin(-x + pi/4) - 2*sin(x + pi/4)=0:=
begin
have : (-2) * sin(x + pi / 4) - (-sin((-2) * x + 1733 * pi / 6) * sin(pi / 6) + cos((-2) * x + 1733 * pi / 6) * cos(pi / 6)) / sin(-x + pi / 4) = -(-sin(pi/6)*sin(-2*x + 1733*pi/6) + cos(pi/6)*cos(-2*x + 1733*pi/6))/sin(-x + pi/4) - 2*sin(x + pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*x + 289*pi) = -sin(-2*x + 1733*pi/6) * sin(pi/6) + cos(-2*x + 1733*pi/6) * cos(pi/6),
{
have : cos(-2*x + 289*pi) = cos((-2*x + 1733*pi/6) + (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * sin(x + pi / 4) + -cos((-2) * x + 289 * pi) / sin(-x + pi / 4) = -2*sin(x + pi/4) - cos(-2*x + 289*pi)/sin(-x + pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*x + 116*pi) = -cos(-2*x + 289*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*x + 116*pi) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos((-2) * x + 116 * pi) / sin(-x + pi / 4) - 2 * sin(x + pi / 4) = -2*sin(x + pi/4) + cos(-2*x + 116*pi)/sin(-x + pi/4),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = cos(-2*x + 116*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*x) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*sin(x + pi/4) = 2*sin(x)*cos(pi/4) + 2*sin(pi/4)*cos(x),
{
have : sin(x + pi/4) = sin(pi/4)*cos(x) + sin(x)*cos(pi/4),
{
have : sin(x + pi/4) = sin((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw sin_add,
ring,
},
linarith,
},
rw this,
rw sin_pi_div_four,
rw cos_pi_div_four,
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
have : -sin(x)**2 + cos(x)**2 = (-sin(x) + cos(x))*(sin(x) + cos(x)),
{
ring_exp,
},
rw this,
have : sin(-x + pi/4) = -sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
{
have : sin(-x+pi/4) = sin((pi/4) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw cos_pi_div_four,
rw sin_pi_div_four,
have : (-sin(x) + cos(x))*(sin(x) + cos(x))/(-sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x)) = sqrt(2)*(sin(x) + cos(x)),
{
have : -sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x) = (sqrt(2)/2) *(-sin(x) + cos(x)),
{
ring,
},
rw this,
field_simp,
ring,
rw sq_sqrt,
repeat {linarith},
},
rw this,
have : 2*sin(x)*(sqrt(2)/2) + 2*(sqrt(2)/2)*cos(x) = sqrt(2)*(sin(x) + cos(x)),
{
ring_exp,
},
rw this,
norm_num,
end


lemma Trigo_5_369_EPCK_extend(h0 : cos(pi/6) ≠ 0) (h1 : cos(pi/4) ≠ 0) (h2 : sin(pi/12) ≠ 0) (h3: cos(pi/18) ≠ 0) (h4 : 2 - sqrt(3) ≠ 0)  (h5 : (sin(5*pi/36)-cos(pi/12)*cos(4*pi/9))≠ 0) (h6 : (-cos(pi/12)*cos(4*pi/9)+sin(5*pi/36))≠ 0) (h7 : (- -cos(2389*pi/12)*cos(4*pi/9)+sin(5*pi/36))≠ 0) (h8 : (cos(4*pi/9)*cos(2389*pi/12)+sin(5*pi/36))≠ 0) (h9 : (cos((-7151)*pi/36)/2+cos(7183*pi/36)/2+sin(5*pi/36))≠ 0) (h10 : (cos(-7151*pi/36)/2+cos(7183*pi/36)/2+sin(5*pi/36))≠ 0) : (sin(pi/18)*sin(pi/12) + sin(2327*pi/36))/(cos(-7151*pi/36)/2 + cos(7183*pi/36)/2 + sin(5*pi/36))=2+sqrt(3):=
begin
have : (sin(pi / 18) * sin(pi / 12) + sin(2327 * pi / 36)) / (cos((-7151) * pi / 36) / 2 + cos(7183 * pi / 36) / 2 + sin(5 * pi / 36)) = (sin(pi/18)*sin(pi/12) + sin(2327*pi/36))/(cos(-7151*pi/36)/2 + cos(7183*pi/36)/2 + sin(5*pi/36)),
{
field_simp at *,
},
have : cos(4*pi/9) * cos(2389*pi/12) = cos(-7151*pi/36) / 2 + cos(7183*pi/36) / 2,
{
rw cos_mul_cos,
have : cos((4*pi/9) + (2389*pi/12)) = cos(7183*pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : cos((4*pi/9) - (2389*pi/12)) = cos(-7151*pi/36),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(4*pi/9) * cos(2389*pi/12)) = cos(4*pi/9)*cos(2389*pi/12),
{
ring,
},
have : (sin(pi / 18) * sin(pi / 12) + sin(2327 * pi / 36)) / (- -cos(2389 * pi / 12) * cos(4 * pi / 9) + sin(5 * pi / 36)) = (sin(pi/18)*sin(pi/12) + sin(2327*pi/36))/(cos(4*pi/9)*cos(2389*pi/12) + sin(5*pi/36)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/12) = -cos(2389*pi/12),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/12) (99),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 18) * sin(pi / 12) + sin(2327 * pi / 36)) / (sin(5 * pi / 36) - cos(pi / 12) * cos(4 * pi / 9)) = (sin(pi/18)*sin(pi/12) + sin(2327*pi/36))/(-cos(pi/12)*cos(4*pi/9) + sin(5*pi/36)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/36) = sin(2327*pi/36),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (13*pi/36) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/36) = cos(5*pi/36),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(5*pi/36) = -sin(pi/18)*sin(pi/12) + cos(pi/18)*cos(pi/12),
{
have : cos(5*pi/36) = cos((pi/12) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
have : cos(4*pi/9) = sin(pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/36) = sin(pi/18)*cos(pi/12) + sin(pi/12)*cos(pi/18),
{
have : sin(5*pi/36) = sin((pi/12) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
ring_exp,
have : cos(pi / 18) * (cos(pi / 12) * (sin(pi / 12) * cos(pi / 18))⁻¹) = cos(pi/12)/sin(pi/12),
{
field_simp,
ring,
},
rw this,
rw ← one_div_div,
rw ← tan_eq_sin_div_cos,
rw tan_pi_div_twelve,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_5_370_SXDW_extend : (-4*(-4*sin(x/9 + y/9)**3 + 3*sin(x/9 + y/9))**3 - 12*sin(x/9 + y/9)**3 + 9*sin(x/9 + y/9))*sin(x - y) + sin(-x + y + 259*pi/2)*cos(x + y)=-cos(2*x):=
begin
have : ((-4) * ((-4) * sin(x / 9 + y / 9) ** 3 + 3 * sin(x / 9 + y / 9)) ** 3 + 3 * ((-4) * sin(x / 9 + y / 9) ** 3 + 3 * sin(x / 9 + y / 9))) * sin(x - y) + sin(-x + y + 259 * pi / 2) * cos(x + y) = (-4*(-4*sin(x/9 + y/9)**3 + 3*sin(x/9 + y/9))**3 - 12*sin(x/9 + y/9)**3 + 9*sin(x/9 + y/9))*sin(x - y) + sin(-x + y + 259*pi/2)*cos(x + y),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/3 + y/3) = -4 * sin(x/9 + y/9) ** 3 + 3 * sin(x/9 + y/9),
{
have : sin(x/3 + y/3) = sin(3*(x/9 + y/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : ((-4) * sin(x / 3 + y / 3) ** 3 + 3 * sin(x / 3 + y / 3)) * sin(x - y) - -sin(-x + y + 259 * pi / 2) * cos(x + y) = (-4*sin(x/3 + y/3)**3 + 3*sin(x/3 + y/3))*sin(x - y) + sin(-x + y + 259*pi/2)*cos(x + y),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x - y) = -sin(-x + y + 259*pi/2),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x - y) (64),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - y) * ((-4) * sin(x / 3 + y / 3) ** 3 + 3 * sin(x / 3 + y / 3)) - cos(x - y) * cos(x + y) = (-4*sin(x/3 + y/3)**3 + 3*sin(x/3 + y/3))*sin(x - y) - cos(x - y)*cos(x + y),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + y) = -4 * sin(x/3 + y/3) ** 3 + 3 * sin(x/3 + y/3),
{
have : sin(x + y) = sin(3*(x/3 + y/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x - y) = sin(x)*cos(y) - cos(x)*sin(y),
{
have : sin(x-y) = sin((x) - (y)),
{
apply congr_arg,
ring,
},
rw sin_sub,
},
rw this,
have : sin(x + y) = sin(x)*cos(y) + cos(x)*sin(y),
{
have : sin(x+y) = sin((x) + (y)),
{
apply congr_arg,
ring,
},
rw sin_add,
},
rw this,
have : (sin(x)*cos(y) - cos(x)*sin(y))*(sin(x)*cos(y) + cos(x)*sin(y)) = sin(x)**2*cos(y)**2 -sin(y)**2*cos(x)**2,
{
ring_exp,
},
rw this,
have : cos(x - y) = cos(x)*cos(y) + sin(x)*sin(y),
{
have : cos(x-y) = cos((x) - (y)),
{
apply congr_arg,
ring,
},
rw cos_sub,
},
rw this,
have : cos(x + y) = cos(x)*cos(y) - sin(x)*sin(y),
{
have : cos(x+y) = cos((x) + (y)),
{
apply congr_arg,
ring,
},
rw cos_add,
},
rw this,
have : (cos(x)*cos(y) + sin(x)*sin(y))*(cos(x)*cos(y) - sin(x)*sin(y)) = cos(x)**2*cos(y)**2 - sin(x)**2*sin(y)**2,
{
ring_exp,
},
rw this,
have : sin(x)**2*cos(y)**2 - sin(y)**2*cos(x)**2 - (cos(x)**2*cos(y)**2 - sin(x)**2*sin(y)**2) = sin(x)**2*cos(y)**2 + sin(x)**2*sin(y)**2 - sin(y)**2*cos(x)**2 - cos(x)**2*cos(y)**2,
{
ring,
},
rw this,
have : sin(x)**2*cos(y)**2 + sin(x)**2*sin(y)**2 = sin(x)**2*(sin(y)**2 + cos(y)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : sin(x)**2*1 - sin(y)**2*cos(x)**2 - cos(x)**2*cos(y)**2 = sin(x)**2*1 - (sin(y)**2*cos(x)**2 + cos(x)**2*cos(y)**2),
{
ring,
},
rw this,
have : sin(y)**2*cos(x)**2 + cos(x)**2*cos(y)**2 = cos(x)**2*(sin(y)**2 + cos(y)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
simp,
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
linarith,
end


lemma Trigo_5_371_UQCA_extend(h0 : sin(2*pi/9) ≥ 0) (h1 : sin(2*pi/9) ≠ 0)  (h2 : sin(4*pi/9)≠ 0) (h3 : sqrt(-sin(8*pi/9)/(2*sin(4*pi/9))+1)≠ 0) (h4 : (2*sin(4*pi/9))≠ 0) (h5 : sqrt(1-sin(8*pi/9)/(2*sin(4*pi/9)))≠ 0) : (-sqrt(3)*cos(535*pi/9) + sin(1679*pi/9))/sqrt(-sin(8*pi/9)/(2*sin(4*pi/9)) + 1)=sqrt(2):=
begin
have : (sqrt 3 * -cos(535 * pi / 9) + sin(1679 * pi / 9)) / sqrt (-sin(8 * pi / 9) / (2 * sin(4 * pi / 9)) + 1) = (-sqrt(3)*cos(535*pi/9) + sin(1679*pi/9))/sqrt(-sin(8*pi/9)/(2*sin(4*pi/9)) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = -cos(535*pi/9),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/18) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * sin(pi / 18) + sin(1679 * pi / 9)) / sqrt (-sin(8 * pi / 9) / (2 * sin(4 * pi / 9)) + 1) = (sqrt(3)*sin(pi/18) + sin(1679*pi/9))/sqrt(-sin(8*pi/9)/(2*sin(4*pi/9)) + 1),
{
field_simp at *,
},
have : cos(pi/18) = sin(1679*pi/9),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/18) (93),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * sin(pi / 18) + cos(pi / 18)) / sqrt (1 - sin(8 * pi / 9) / (2 * sin(4 * pi / 9))) = (sqrt(3)*sin(pi/18) + cos(pi/18))/sqrt(-sin(8*pi/9)/(2*sin(4*pi/9)) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = sin(8*pi/9) / ( 2 * sin(4*pi/9) ),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
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
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
have : cos(4*pi/9) = -sin(2*pi/9)**2 + cos(2*pi/9)**2,
{
have : cos(4*pi/9) = cos(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
rw cos_sq',
have : 1 - (-sin(2*pi/9)**2 + (1 - sin(2*pi/9)**2)) = 2*sin(2*pi/9)**2,
{
ring,
},
rw this,
rw sqrt_mul,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_5_372_DLNH_extend(h0 : -cos 1 + sin 1 ≥ 0) (h1 : cos 1 ≥ 0) (h2 : 0 ≤ 2)  (h3 : cos(2)≠ 0) (h4 : (2*cos(2))≠ 0) : 2*sqrt(-(1 - 2*sin(2 + 263*pi/4)**2)/(2*cos(2)) + 1) + sqrt(2*cos(2) + 2)=2*sin(1):=
begin
have : cos(4 + 263*pi/2) = 1 - 2 * sin(2 + 263*pi/4) ** 2,
{
have : cos(4 + 263*pi/2) = cos(2*(2 + 263*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : sin(4) = cos(4 + 263*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (4) (65),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sqrt (1 - sin(4) / (2 * cos(2))) + sqrt (2 * cos(2) + 2) = 2*sqrt(-sin(4)/(2*cos(2)) + 1) + sqrt(2*cos(2) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2) = sin(4) / ( 2 * cos(2) ),
{
have : sin(4) = sin(2*(2)),
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
have : 1 - sin(2) = sin(1)**2 + cos(1)**2 - sin(2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(2) = 2*sin(1)*cos(1),
{
have : sin(2) = sin(2*(1)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(1)**2 + cos(1)**2 - 2*sin(1)*cos(1) = (-cos(1) + sin(1))**2,
{
ring_exp,
},
rw this,
have : 2*cos(2) + 2 = 4*cos(1)**2,
{
have : cos(1)**2 = cos(2)/2 + 1/2,
{
have : cos(2) = cos(2*(1)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
linarith,
},
rw this,
rw sqrt_mul,
repeat {rw sqrt_sq_eq_abs},
rw abs_eq_self.mpr h0,
rw abs_eq_self.mpr h1,
have : sqrt(4) = sqrt(2**2),
{
apply congr_arg,
ring,
},
rw this,
rw sqrt_sq,
ring_exp,
repeat {linarith},
end


lemma Trigo_5_373_AGWJ_extend(h0 : sin(pi/7) ≠ 0)  : -sin(3337*pi/14) + cos(4*pi/7) + cos(12*pi/7)=-1/2:=
begin
have : cos(1301*pi/7) = sin(3337*pi/14),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (1301*pi/7) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(6*pi/7) = -cos(1301*pi/7),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (6*pi/7) (92),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(12 * pi / 7) + cos(4 * pi / 7) + cos(6 * pi / 7) = cos(6*pi/7) + cos(4*pi/7) + cos(12*pi/7),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/7) = cos(12*pi/7),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (2*pi/7) (1),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/7) + cos(4*pi/7) + cos(6*pi/7) = (2*sin(pi/7)*cos(6*pi/7) + 2*sin(pi/7)*cos(4*pi/7) + 2*sin(pi/7)*cos(2*pi/7))/(2*sin(pi/7)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : 2*sin(pi/7)*cos(6*pi/7) = sin(-5*pi/7) + sin(pi),
{
have : sin(pi/7)*cos(6*pi/7) = sin(-5*pi/7)/2 + sin(pi)/2,
{
rw sin_mul_cos,
have : sin((pi/7) + (6*pi/7)) = sin(pi),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/7) - (6*pi/7)) = sin(-5*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : 2*sin(pi/7)*cos(4*pi/7) = sin(-3*pi/7) + sin(5*pi/7),
{
have : sin(pi/7)*cos(4*pi/7) = sin(-3*pi/7)/2 + sin(5*pi/7)/2,
{
rw sin_mul_cos,
have : sin((pi/7) + (4*pi/7)) = sin(5*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/7) - (4*pi/7)) = sin(-3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : 2*sin(pi/7)*cos(2*pi/7) = sin(-pi/7) + sin(3*pi/7),
{
have : sin(pi/7)*cos(2*pi/7) = sin(-pi/7)/2 + sin(3*pi/7)/2,
{
rw sin_mul_cos,
have : sin((pi/7) + (2*pi/7)) = sin(3*pi/7),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/7) - (2*pi/7)) = sin(-pi/7),
{
apply congr_arg,
ring,
},
rw this,
},
linarith,
},
rw this,
have : sin(-3*pi/7) = -sin(3*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-3*pi/7) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-5*pi/7) = -sin(5*pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/7) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(-pi/7) = -sin(pi/7),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/7) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_5_374_VVQR_extend(h0 : cos(4*pi/9) ≠ 0) (h1 : cos(2*pi/9) ≠ 0) (h2 : 1 - tan(2*pi/9) * tan(4*pi/9) ≠ 0)  (h3 : tan(1531*pi/18)≠ 0) (h4 : cos(770*pi/9)≠ 0) (h5 : cos(pi/2)≠ 0) (h6 : (1+tan(770*pi/9)*tan(pi/2))≠ 0) (h7 : ((tan(770*pi/9)-tan(pi/2))/(1+tan(770*pi/9)*tan(pi/2)))≠ 0) (h8 : (-tan(pi/2)+tan(770*pi/9))≠ 0) (h9 : cos(770*pi/9)≠ 0) (h10 : cos(pi/2)≠ 0) (h11 : tan((770*pi/9)-(pi/2))≠ 0) (h12 : 1+tan(770*pi/9)*tan(pi/2)≠ 0) : -sqrt(3)*tan(2*pi/9)/tan(1531*pi/18) + tan(2*pi/9) + 1/tan(1531*pi/18)=-sqrt(3):=
begin
have : -sqrt 3 * ((tan(770 * pi / 9) - tan(pi / 2)) / tan(1531 * pi / 18) - 1 + 1) * tan(2 * pi / 9) / (-tan(pi / 2) + tan(770 * pi / 9)) + ((tan(770 * pi / 9) - tan(pi / 2)) / tan(1531 * pi / 18) - 1 + 1) / (-tan(pi / 2) + tan(770 * pi / 9)) + tan(2 * pi / 9) = -sqrt(3)*tan(2*pi/9)/tan(1531*pi/18) + tan(2*pi/9) + 1/tan(1531*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(770*pi/9) * tan(pi/2) = ( tan(770*pi/9) - tan(pi/2) ) / tan(1531*pi/18) - 1,
{
rw tan_mul_tan,
have : tan((770*pi/9) - (pi/2)) = tan(1531*pi/18),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(770*pi/9) * tan(pi/2)) = tan(pi/2)*tan(770*pi/9),
{
ring,
},
conv {to_lhs, rw this,},
have : -sqrt 3 * tan(2 * pi / 9) / ((tan(770 * pi / 9) - tan(pi / 2)) / (1 + tan(770 * pi / 9) * tan(pi / 2))) + tan(2 * pi / 9) + 1 / ((tan(770 * pi / 9) - tan(pi / 2)) / (1 + tan(770 * pi / 9) * tan(pi / 2))) = -sqrt(3)*(tan(pi/2)*tan(770*pi/9) + 1)*tan(2*pi/9)/(-tan(pi/2) + tan(770*pi/9)) + (tan(pi/2)*tan(770*pi/9) + 1)/(-tan(pi/2) + tan(770*pi/9)) + tan(2*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(1531*pi/18) = ( tan(770*pi/9) - tan(pi/2) ) / ( 1 + tan(770*pi/9) * tan(pi/2) ),
{
have : tan(1531*pi/18) = tan((770*pi/9) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * tan(2 * pi / 9) * (1 / tan(1531 * pi / 18)) + tan(2 * pi / 9) + 1 / tan(1531 * pi / 18) = -sqrt(3)*tan(2*pi/9)/tan(1531*pi/18) + tan(2*pi/9) + 1/tan(1531*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(4*pi/9) = 1 / tan(1531*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (4*pi/9) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(2*pi/9) + tan(4*pi/9) = (-tan(2*pi/9)*tan(4*pi/9) + 1)*tan(2*pi/3),
{
rw tan_add_tan,
have : tan((2*pi/9) + (4*pi/9)) = tan(2*pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : tan(2*pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : (-tan(2*pi/9)*tan(4*pi/9) + 1)*-tan(pi/3) = tan(2*pi/9)*tan(pi/3)*tan(4*pi/9) - tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
norm_num,
ring_exp,
end


lemma Trigo_5_375_EZCK_extend(h0 : cos(pi/10) ≠ 0) (h1 : 1 - tan(pi/10) * tan(pi/15) ≠ 0) (h2 : cos(pi/15) ≠ 0)  (h3 : cos((pi/5)/2)≠ 0) (h4 : sin(pi/5)≠ 0) (h5 : cos(629*pi/30)≠ 0) (h6 : ((1-tan(629*pi/30)**2)*sin(pi/5))≠ 0) (h7 : (1-tan(629*pi/30)**2)≠ 0) : 2*(-1 + cos(pi/5))*tan(629*pi/30)/((1 - tan(629*pi/30)**2)*sin(pi/5)) - 2*sqrt(3)*tan(629*pi/30)/(1 - tan(629*pi/30)**2) + sqrt(3)*(1 - cos(pi/5))/sin(pi/5)=1:=
begin
have : -(1 - cos(pi / 5)) * (2 * tan(629 * pi / 30) / (1 - tan(629 * pi / 30) ** 2)) / sin(pi / 5) - sqrt 3 * (2 * tan(629 * pi / 30) / (1 - tan(629 * pi / 30) ** 2)) + sqrt 3 * (1 - cos(pi / 5)) / sin(pi / 5) = 2*(-1 + cos(pi/5))*tan(629*pi/30)/((1 - tan(629*pi/30)**2)*sin(pi/5)) - 2*sqrt(3)*tan(629*pi/30)/(1 - tan(629*pi/30)**2) + sqrt(3)*(1 - cos(pi/5))/sin(pi/5),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(629*pi/15) = 2 * tan(629*pi/30) / ( 1 - tan(629*pi/30) ** 2 ),
{
have : tan(629*pi/15) = tan(2*(629*pi/30)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -((1 - cos(pi / 5)) / sin(pi / 5)) * tan(629 * pi / 15) - sqrt 3 * tan(629 * pi / 15) + sqrt 3 * ((1 - cos(pi / 5)) / sin(pi / 5)) = -(1 - cos(pi/5))*tan(629*pi/15)/sin(pi/5) - sqrt(3)*tan(629*pi/15) + sqrt(3)*(1 - cos(pi/5))/sin(pi/5),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) = ( 1 - cos(pi/5) ) / sin(pi/5),
{
have : tan(pi/10) = tan((pi/5)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -tan(629 * pi / 15) * tan(pi / 10) + sqrt 3 * -tan(629 * pi / 15) + sqrt 3 * tan(pi / 10) = -tan(pi/10)*tan(629*pi/15) - sqrt(3)*tan(629*pi/15) + sqrt(3)*tan(pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/15) = -tan(629*pi/15),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (pi/15) (42),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : sqrt(3)*tan(pi/15) + sqrt(3)*tan(pi/10) = sqrt(3)*(tan(pi/15) + tan(pi/10)),
{
ring_exp,
},
rw this,
have : tan(pi/15) + tan(pi/10) = (-tan(pi/15)*tan(pi/10) + 1)*tan(pi/6),
{
rw add_comm,
rw tan_add_tan,
have : tan((pi/10) + (pi/15)) = tan(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/15)*tan(pi/10) + 1)*tan(pi/6) = -tan(pi/15)*tan(pi/10)*tan(pi/6) + tan(pi/6),
{
ring_exp,
},
rw this,
rw tan_pi_div_six,
have : sqrt(3)*(-tan(pi/15)*tan(pi/10)*(sqrt(3)/3) + sqrt(3)/3) = -tan(pi/15)*tan(pi/10) + 1,
{
ring_exp,
rw sq_sqrt,
ring_exp,
linarith,
},
rw this,
norm_num,
end


lemma Trigo_5_376_SNED_extend(h0 : cos(pi/4) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : -sin(x) + cos(x) ≠ 0) (h3 : sin(2*x) + 1 ≠ 0)  (h4 : (2*cos(-x+pi/4)**2)≠ 0) (h5 : (2*cos(-x+pi/4)**2*cos(x+pi/4))≠ 0) (h6 : cos(x+pi/4)≠ 0) (h7 : (2*sin(-x+235*pi/4)**2*cos(x+pi/4))≠ 0) : sin(x + pi/4)*cos(2*x + 100*pi)/(2*sin(-x + 235*pi/4)**2*cos(x + pi/4))=1:=
begin
have : cos(2*x) = cos(2*x + 100*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (2*x) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + pi/4) = sin(-x + 235*pi/4),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-x + pi/4) (29),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2 * x) * (sin(x + pi / 4) / cos(x + pi / 4)) / (2 * cos(-x + pi / 4) ** 2) = sin(x + pi/4)*cos(2*x)/(2*cos(-x + pi/4)**2*cos(x + pi/4)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi/4) = sin(x + pi/4) / cos(x + pi/4),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi/4) = (tan(x) + tan(pi/4))/(-tan(pi/4)*tan(x) + 1),
{
have : tan(x + pi/4) = tan((x) + (pi/4)),
{
apply congr_arg,
ring,
},
rw tan_add,
field_simp,
ring_exp,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
rw tan_eq_sin_div_cos,
have : sin(x)/cos(x) + 1 = (sin(x) + cos(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : -1*(sin(x)/cos(x)) + 1 = (-sin(x) + cos(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
have : -sin(x)**2 + cos(x)**2 = (-sin(x) + cos(x))*(sin(x) + cos(x)),
{
ring_exp,
},
rw this,
have : 2*cos(-x + pi/4)**2 = cos(-2*x + pi/2) + 1,
{
have : cos(-x + pi/4)**2 = cos(-2*x + pi/2)/2 + 1/2,
{
have : cos(-2*x + pi/2) = cos(2*(-x + pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
linarith,
},
rw this,
have : cos(-2*x + pi/2) = sin(2*x),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*x + pi/2) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : (-sin(x) + cos(x))*(sin(x) + cos(x))*((sin(x) + cos(x))/cos(x)/((-sin(x) + cos(x))/cos(x))) = (-sin(x) + cos(x))*(sin(x) + cos(x))**2/cos(x)/((-sin(x) + cos(x))/cos(x)),
{
ring,
},
rw this,
have : (sin(x) + cos(x))**2 = sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : 2*sin(x)*cos(x) = sin(2*x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
field_simp,
left,
ring_exp,
end


lemma Trigo_5_377_VMLJ_extend(h0 : sin(pi/5) ≠ 0)  : -1/2 + cos(3*pi/10)**2 + cos(859*pi/5)/2=1/4:=
begin
have : (-1) / 2 + cos(3 * pi / 10) ** 2 + cos(859 * pi / 5) / 2 = -1/2 + cos(3*pi/10)**2 + cos(859*pi/5)/2,
{
field_simp at *,
},
have : cos(pi/5) = cos(859*pi/5),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (pi/5) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (2 * cos(3 * pi / 10) ** 2 - 1) / 2 + cos(pi / 5) / 2 = -1/2 + cos(3*pi/10)**2 + cos(pi/5)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*pi/5) = 2 * cos(3*pi/10) ** 2 - 1,
{
have : cos(3*pi/5) = cos(2*(3*pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 5) / 2 + cos(3 * pi / 5) / 2 = cos(3*pi/5)/2 + cos(pi/5)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/5) * cos(pi/5) = cos(pi/5) / 2 + cos(3*pi/5) / 2,
{
rw cos_mul_cos,
have : cos((2*pi/5) + (pi/5)) = cos(3*pi/5),
{
apply congr_arg,
ring,
},
rw this,
have : cos((2*pi/5) - (pi/5)) = cos(pi/5),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(2*pi/5) * cos(pi/5)) = cos(pi/5)*cos(2*pi/5),
{
ring,
},
conv {to_lhs, rw this,},
have : cos(pi/5) = sin(2*pi/5)/(2*sin(pi/5)),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
rw div_mul_eq_mul_div,
have : sin(2*pi/5)*cos(2*pi/5) = sin(4*pi/5)/2,
{
have : sin(4*pi/5) = 2*sin(2*pi/5)*cos(2*pi/5),
{
have : sin(4*pi/5) = sin(2*(2*pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/5) = sin(pi/5),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4*pi/5) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_378_LZPJ_extend(h0 : tan(31*pi/90) ≠ 0)  (h1 : cos(pi/4)≠ 0) (h2 : cos(7*pi/45)≠ 0) (h3 : tan((pi/4)+(7*pi/45))≠ 0) (h4 : 1-tan(pi/4)*tan(7*pi/45)≠ 0) (h5 : tan(73*pi/180)≠ 0) : (sin(pi/30)*cos(-pi/6) - sin(-pi/6)*sin(547*pi/15))**2 + sin(3*pi/10)**2 + ((-tan(pi/4) - tan(7*pi/45))/tan(73*pi/180) + 1)*tan(31*pi/90)=2:=
begin
have : cos(pi/30) = sin(547*pi/15),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/30) (18),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 30) * cos(-pi / 6) - sin(-pi / 6) * cos(pi / 30)) ** 2 + sin(3 * pi / 10) ** 2 + (-(tan(pi / 4) + tan(7 * pi / 45)) / tan(73 * pi / 180) + 1) * tan(31 * pi / 90) = (sin(pi/30)*cos(-pi/6) - sin(-pi/6)*cos(pi/30))**2 + sin(3*pi/10)**2 + ((-tan(pi/4) - tan(7*pi/45))/tan(73*pi/180) + 1)*tan(31*pi/90),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/4) * tan(7*pi/45) = -( tan(pi/4) + tan(7*pi/45) ) / tan(73*pi/180) + 1,
{
rw tan_mul_tan',
have : tan((pi/4) + (7*pi/45)) = tan(73*pi/180),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(pi/4) * tan(7*pi/45))*tan(31*pi/90) = tan(7*pi/45)*tan(pi/4)*tan(31*pi/90),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(pi/5) = sin(pi/30) * cos(-pi/6) - sin(-pi/6) * cos(pi/30),
{
have : sin(pi/5) = sin((pi/30) - (-pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/5)**2 = 1/2 - cos(2*pi/5)/2,
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
have : sin(3*pi/10)**2 = 1/2 - cos(3*pi/5)/2,
{
have : cos(3*pi/5) = cos(2*(3*pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(3*pi/5) = -cos(2*pi/5),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/5) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(7*pi/45) = 1/tan(31*pi/90),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/45) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_four,
field_simp,
ring_exp,
end


lemma Trigo_5_379_PLEF_extend(h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/18) ≠ 0)  (h2 : cos(pi/18)≠ 0) : (-sqrt(3) + ((sin(-41*pi/18)*cos(2*pi) + sin(2*pi)*cos(-41*pi/18))*cos(pi/3) + sin(pi/3)*cos(-5*pi/18))/cos(pi/18))*cos(5*pi/18)=-1:=
begin
have : (-sqrt 3 + ((sin((-41) * pi / 18) * cos(2 * pi) + sin(2 * pi) * cos((-41) * pi / 18)) * cos(pi / 3) + sin(pi / 3) * cos((-5) * pi / 18)) / cos(pi / 18)) * cos(5 * pi / 18) = (-sqrt(3) + ((sin(-41*pi/18)*cos(2*pi) + sin(2*pi)*cos(-41*pi/18))*cos(pi/3) + sin(pi/3)*cos(-5*pi/18))/cos(pi/18))*cos(5*pi/18),
{
field_simp at *,
},
have : sin(-5*pi/18) = sin(-41*pi/18) * cos(2*pi) + sin(2*pi) * cos(-41*pi/18),
{
have : sin(-5*pi/18) = sin((-41*pi/18) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sqrt 3 + (sin((-5) * pi / 18) * cos(pi / 3) + sin(pi / 3) * cos((-5) * pi / 18)) / cos(pi / 18)) * cos(5 * pi / 18) = (-sqrt(3) + (sin(-5*pi/18)*cos(pi/3) + sin(pi/3)*cos(-5*pi/18))/cos(pi/18))*cos(5*pi/18),
{
field_simp at *,
},
have : sin(pi/18) = sin(-5*pi/18) * cos(pi/3) + sin(pi/3) * cos(-5*pi/18),
{
have : sin(pi/18) = sin((-5*pi/18) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(pi / 18) / cos(pi / 18) - sqrt 3) * cos(5 * pi / 18) = (-sqrt(3) + sin(pi/18)/cos(pi/18))*cos(5*pi/18),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = sin(pi/18) / cos(pi/18),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sqrt(3) = tan(pi/3),
{
field_simp,
},
rw this,
rw sub_eq_neg_add,
have : -tan(pi/3) + tan(pi/18) = sin(-5*pi/18)/(cos(pi/18)*cos(pi/3)),
{
rw neg_add_eq_sub,
rw tan_sub_tan',
have : sin((pi/18) - (pi/3)) = sin(-5*pi/18),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
rw this,
have : sin(-5*pi/18) = -sin(5*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw div_mul_eq_mul_div,
have : -sin(5*pi/18)*cos(5*pi/18) = -sin(5*pi/9)/2,
{
have : sin(5*pi/9) = 2*sin(5*pi/18)*cos(5*pi/18),
{
have : sin(5*pi/9) = sin(2*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(5*pi/9) = cos(pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_5_380_ZVBA_extend(h0 : cos(x)**2 ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (-cos((-2)*x+171*pi)+1)≠ 0) (h3 : (1-cos(-2*x+171*pi))≠ 0) (h4 : (-sin(pi)*sin(-2*x+172*pi)-cos(pi)*cos(-2*x+172*pi)+1)≠ 0) (h5 : (1-(sin((-2)*x+172*pi)*sin(pi)+cos((-2)*x+172*pi)*cos(pi)))≠ 0) (h6 : cos(x - pi/3)≠ 0) (h7 : cos(-pi/3)≠ 0) (h8 : (tan(-pi/3)*tan(x-pi/3)+1)≠ 0) (h9 : (1+tan(x-pi/3)*tan(-pi/3))≠ 0) : (sin(pi)*sin(-2*x + 172*pi) + cos(pi)*cos(-2*x + 172*pi) + 1)/(-sin(pi)*sin(-2*x + 172*pi) - cos(pi)*cos(-2*x + 172*pi) + 1)=(tan(x - pi/3) - tan(-pi/3))**2/(tan(-pi/3)*tan(x - pi/3) + 1)**2:=
begin
have : ((tan(x - pi / 3) - tan(-pi / 3)) / (1 + tan(x - pi / 3) * tan(-pi / 3))) ** 2 = (tan(x - pi/3) - tan(-pi/3))**2/(tan(-pi/3)*tan(x - pi/3) + 1)**2,
{
field_simp at *,
repeat {left},
ring,
},
conv {to_rhs, rw ← this,},
have : tan(x) = ( tan(x - pi/3) - tan(-pi/3) ) / ( 1 + tan(x - pi/3) * tan(-pi/3) ),
{
have : tan(x) = tan((x - pi/3) - (-pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_rhs, rw ← this,},
have : (sin((-2) * x + 172 * pi) * sin(pi) + cos((-2) * x + 172 * pi) * cos(pi) + 1) / (1 - (sin((-2) * x + 172 * pi) * sin(pi) + cos((-2) * x + 172 * pi) * cos(pi))) = (sin(pi)*sin(-2*x + 172*pi) + cos(pi)*cos(-2*x + 172*pi) + 1)/(-sin(pi)*sin(-2*x + 172*pi) - cos(pi)*cos(-2*x + 172*pi) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*x + 171*pi) = sin(-2*x + 172*pi) * sin(pi) + cos(-2*x + 172*pi) * cos(pi),
{
have : cos(-2*x + 171*pi) = cos((-2*x + 172*pi) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 - -cos((-2) * x + 171 * pi)) / (-cos((-2) * x + 171 * pi) + 1) = (cos(-2*x + 171*pi) + 1)/(1 - cos(-2*x + 171*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -cos(-2*x + 171*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*x) (85),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
have : 1 - (-sin(x)**2 + cos(x)**2) = sin(x)**2 + cos(x)**2 - (-sin(x)**2 + cos(x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(x)**2 + cos(x)**2 - (-sin(x)**2 + cos(x)**2) = 2*sin(x)**2,
{
ring,
},
rw this,
have : -sin(x)**2 + cos(x)**2 + 1 = -sin(x)**2 + cos(x)**2 + (sin(x)**2 + cos(x)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : -sin(x)**2 + cos(x)**2 + (sin(x)**2 + cos(x)**2) = 2*cos(x)**2,
{
ring,
},
rw this,
rw tan_eq_sin_div_cos,
rw div_pow,
field_simp,
ring_exp,
end


lemma Trigo_5_381_UFKP_extend(h0 : cos(x/2) ≠ 0) (h1 : sin(x/2) ≠ 0) (h2 : cos(x) ≠ 0)  (h3 : tan(x/2)≠ 0) (h4 : (-tan(x/2)+1/tan(x/2))≠ 0) (h5 : cos((x)/2)≠ 0) (h6 : (1+cos(x))≠ 0) (h7 : (sin(x)/(1+cos(x)))≠ 0) (h8 : (-(sin(x)/(1+cos(x)))+1/(sin(x)/(1+cos(x))))≠ 0) (h9 : ((cos(x)+1)/sin(x)-sin(x)/(cos(x)+1))≠ 0) (h10 : (cos(x)+1)≠ 0) (h11 : sin(x)≠ 0) (h12 : ((cos(x)+1)/ -sin(-x+88*pi)- -sin(-x+88*pi)/(cos(x)+1))≠ 0) (h13 : (-(cos(x)+1)/sin(-x+88*pi)+sin(-x+88*pi)/(cos(x)+1))≠ 0) (h14 : -sin(-x+88*pi)≠ 0) (h15 : sin(-x+88*pi)≠ 0) : cos(-x + 109*pi)**2/(-(cos(x) + 1)/sin(-x + 88*pi) + sin(-x + 88*pi)/(cos(x) + 1))=1/4*sin(2*x):=
begin
have : cos(-x + 109 * pi) ** 2 / ((cos(x) + 1) / -sin(-x + 88 * pi) - -sin(-x + 88 * pi) / (cos(x) + 1)) = cos(-x + 109*pi)**2/(-(cos(x) + 1)/sin(-x + 88*pi) + sin(-x + 88*pi)/(cos(x) + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -sin(-x + 88*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (x) (44),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 109 * pi) ** 2 / (-(sin(x) / (1 + cos(x))) + 1 / (sin(x) / (1 + cos(x)))) = cos(-x + 109*pi)**2/((cos(x) + 1)/sin(x) - sin(x)/(cos(x) + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x/2) = sin(x) / ( 1 + cos(x) ),
{
have : tan(x/2) = tan((x)/2),
{
apply congr_arg,
ring,
},
rw tan_div_two',
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (-cos(-x + 109 * pi)) ** 2 / (-tan(x / 2) + 1 / tan(x / 2)) = cos(-x + 109*pi)**2/(-tan(x/2) + 1/tan(x/2)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -cos(-x + 109*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (x) (54),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw one_div_div,
have : -(sin(x/2)/cos(x/2)) + cos(x/2)/sin(x/2) = (-sin(x/2)**2 + cos(x/2)**2)/(sin(x/2)*cos(x/2)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : -sin(x/2)**2 + cos(x/2)**2 = cos(x),
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : sin(x/2)*cos(x/2) = sin(x)/2,
{
have : sin(x) = 2*sin(x/2)*cos(x/2),
{
have : sin(x) = sin(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_382_HMEV_extend(h0 : cos(pi/3) ≠ 0) (h1 : 1 + tan(pi/3) * tan(pi/18) ≠ 0) (h2 : cos(pi/18) ≠ 0) (h3 : tan(5*π/18) ≠ 0)  (h4 : cos(7*pi/18)≠ 0) (h5 : cos(pi/6)≠ 0) (h6 : (1+tan(pi/6)*tan(7*pi/18))≠ 0) (h7 : (1+tan(7*pi/18)*tan(pi/6))≠ 0) (h8 : cos(7*pi/18)≠ 0) (h9 : cos(pi/6)≠ 0) (h10 : tan((7*pi/18)+(pi/6))≠ 0) (h11 : 1-tan(7*pi/18)*tan(pi/6)≠ 0) (h12 : (1+(-(tan(7*pi/18)+tan(pi/6))/tan(5*pi/9)+1))≠ 0) (h13 : ((-tan(7*pi/18)-tan(pi/6))/tan(5*pi/9)+2)≠ 0) (h14 : tan(5*pi/9)≠ 0) (h15 : tan(742*pi/9)≠ 0) : -sqrt(3)/tan(742*pi/9) + (-tan(pi/6) + tan(7*pi/18))*(-1/tan(742*pi/9) + sqrt(3))/((-tan(7*pi/18) - tan(pi/6))/tan(5*pi/9) + 2)=1:=
begin
have : -sqrt 3 * (1 / tan(742 * pi / 9)) + (-(1 / tan(742 * pi / 9)) + sqrt 3) * (-tan(pi / 6) + tan(7 * pi / 18)) / ((-tan(7 * pi / 18) - tan(pi / 6)) / tan(5 * pi / 9) + 2) = -sqrt(3)/tan(742*pi/9) + (-tan(pi/6) + tan(7*pi/18))*(-1/tan(742*pi/9) + sqrt(3))/((-tan(7*pi/18) - tan(pi/6))/tan(5*pi/9) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/18) = 1 / tan(742*pi/9),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/18) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sqrt 3 * tan(pi / 18) + (-tan(pi / 18) + sqrt 3) * (-tan(pi / 6) + tan(7 * pi / 18)) / (1 + (-(tan(7 * pi / 18) + tan(pi / 6)) / tan(5 * pi / 9) + 1)) = -sqrt(3)*tan(pi/18) + (-tan(pi/18) + sqrt(3))*(-tan(pi/6) + tan(7*pi/18))/((-tan(7*pi/18) - tan(pi/6))/tan(5*pi/9) + 2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/18) * tan(pi/6) = -( tan(7*pi/18) + tan(pi/6) ) / tan(5*pi/9) + 1,
{
rw tan_mul_tan',
have : tan((7*pi/18) + (pi/6)) = tan(5*pi/9),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(7*pi/18) * tan(pi/6)) = tan(pi/6)*tan(7*pi/18),
{
ring,
},
conv {to_lhs, rw this,},
have : (-tan(pi / 18) + sqrt 3) * ((tan(7 * pi / 18) - tan(pi / 6)) / (1 + tan(7 * pi / 18) * tan(pi / 6))) - sqrt 3 * tan(pi / 18) = -sqrt(3)*tan(pi/18) + (-tan(pi/18) + sqrt(3))*(-tan(pi/6) + tan(7*pi/18))/(1 + tan(pi/6)*tan(7*pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/9) = ( tan(7*pi/18) - tan(pi/6) ) / ( 1 + tan(7*pi/18) * tan(pi/6) ),
{
have : tan(2*pi/9) = tan((7*pi/18) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sqrt(3) = tan(pi/3),
{
field_simp,
},
rw this,
have : -tan(pi/18) + tan(pi/3) = (tan(pi/18)*tan(pi/3) + 1)*tan(5*pi/18),
{
rw neg_add_eq_sub,
rw tan_sub_tan,
have : tan((pi/3) - (pi/18)) = tan(5*pi/18),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : tan(2*pi/9) = 1/tan(5*pi/18),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_5_383_OJSQ_extend(h0 : cos(pi/4) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : -sin(x) + cos(x) ≠ 0)  (h3 : tan(-x+pi/4)≠ 0) : (-sin(2*pi)*sin(2*x + 43*pi) + sin(201*pi/2)*cos(2*x + 2*pi))/tan(-x + pi/4)=1+sin(2*x):=
begin
have : cos(2*pi) = sin(201*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi) (51),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * pi) * -sin(2 * x + 43 * pi) + cos(2 * pi) * cos(2 * x + 2 * pi)) / tan(-x + pi / 4) = (-sin(2*pi)*sin(2*x + 43*pi) + cos(2*pi)*cos(2*x + 2*pi))/tan(-x + pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(2*x + 2*pi) = -sin(2*x + 43*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*x + 2*pi) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(2 * x + 2 * pi) * sin(2 * pi) + cos(2 * x + 2 * pi) * cos(2 * pi)) / tan(-x + pi / 4) = (sin(2*pi)*sin(2*x + 2*pi) + cos(2*pi)*cos(2*x + 2*pi))/tan(-x + pi/4),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = sin(2*x + 2*pi) * sin(2*pi) + cos(2*x + 2*pi) * cos(2*pi),
{
have : cos(2*x) = cos((2*x + 2*pi) - (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-x + pi/4) = (-tan(x) + tan(pi/4))/(tan(pi/4)*tan(x) + 1),
{
have : tan(-x + pi/4) = tan((pi/4) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
field_simp,
ring_exp,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
rw tan_eq_sin_div_cos,
have : 1*(sin(x)/cos(x)) + 1 = (sin(x) + cos(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : -(sin(x)/cos(x)) + 1 = (-sin(x) + cos(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : cos(2*x) = -sin(x)**2 + cos(x)**2,
{
have : cos(2*x) = cos(2*(x)),
{
apply congr_arg,
ring,
},
rw cos_two_mul',
ring,
},
rw this,
have : -sin(x)**2 + cos(x)**2 = (-sin(x) + cos(x))*(sin(x) + cos(x)),
{
ring_exp,
},
rw this,
have : (-sin(x) + cos(x))*(sin(x) + cos(x))/((-sin(x) + cos(x))/cos(x)/((sin(x) + cos(x))/cos(x))) = (-sin(x) + cos(x))*(sin(x) + cos(x))**2/((-sin(x) + cos(x))/cos(x)*cos(x)),
{
field_simp,
ring,
},
rw this,
have : (sin(x) + cos(x))**2 = sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x),
{
ring_exp,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
rw sin_sq_add_cos_sq,
field_simp,
ring_exp,
end


lemma Trigo_5_384_HVMF_extend(h0 : cos(x + pi/6) ≠ 0) (h1 : cos(-x + pi/6) ≠ 0) (h2 : 1 - tan(x + pi/6) * tan(-x + pi/6) ≠ 0)  (h3 : cos(x + pi/6)≠ 0) (h4 : cos(-x + pi/6)≠ 0) (h5 : tan((x + pi/6)+(-x + pi/6))≠ 0) (h6 : 1-tan(x + pi/6)*tan(-x + pi/6)≠ 0) (h7 : tan(pi/3)≠ 0) (h8 : cos(-x + pi/6)≠ 0) (h9 : cos(x + pi/6)≠ 0) (h10 : 1 - tan(-x + pi/6) * tan(x + pi/6)≠ 0) : sqrt(3)*tan(-x + 55*pi/6)*tan(x + pi/6) + tan(-x + 55*pi/6) + tan(x + pi/6)=sqrt(3):=
begin
have : sqrt 3 * tan(-x + 55 * pi / 6) * tan(x + pi / 6) + tan(-x + 55 * pi / 6) + tan(x + pi / 6) = sqrt(3)*tan(-x + 55*pi/6)*tan(x + pi/6) + tan(-x + 55*pi/6) + tan(x + pi/6),
{
field_simp at *,
},
have : tan(-x + pi/6) = tan(-x + 55*pi/6),
{
rw tan_eq_tan_add_int_mul_pi (-x + pi/6) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * ((-1) * ((-tan(-x + pi / 6) * tan(x + pi / 6) + 1) * tan(pi / 3)) / tan(pi / 3) + 1) + tan(-x + pi / 6) + tan(x + pi / 6) = sqrt(3)*tan(-x + pi/6)*tan(x + pi/6) + tan(-x + pi/6) + tan(x + pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-x + pi/6) + tan(x + pi/6) = ( -tan(-x + pi/6) * tan(x + pi/6) + 1 ) * tan(pi/3),
{
rw tan_add_tan,
have : tan((-x + pi/6) + (x + pi/6)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -1*(tan(-x + pi/6) + tan(x + pi/6)) = (-tan(-x+pi/6)-tan(x+pi/6)),
{
ring,
},
conv {to_lhs, rw this,},
have : sqrt 3 * (-(tan(x + pi / 6) + tan(-x + pi / 6)) / tan(pi / 3) + 1) + tan(-x + pi / 6) + tan(x + pi / 6) = sqrt(3)*((-tan(-x + pi/6) - tan(x + pi/6))/tan(pi/3) + 1) + tan(-x + pi/6) + tan(x + pi/6),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x + pi/6) * tan(-x + pi/6) = -( tan(x + pi/6) + tan(-x + pi/6) ) / tan(pi/3) + 1,
{
rw tan_mul_tan',
have : tan((x + pi/6) + (-x + pi/6)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sqrt(3)*(tan(x + pi/6) * tan(-x + pi/6)) = sqrt(3)*tan(-x+pi/6)*tan(x+pi/6),
{
ring,
},
conv {to_lhs, rw this,},
rw add_assoc,
have : tan(-x + pi/6) + tan(x + pi/6) = (-tan(-x + pi/6)*tan(x + pi/6) + 1)*tan(pi/3),
{
rw add_comm,
rw tan_add_tan,
have : tan((x + pi/6) + (-x + pi/6)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(-x + pi/6)*tan(x + pi/6) + 1)*tan(pi/3) = -tan(pi/3)*tan(-x + pi/6)*tan(x + pi/6) + tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
norm_num,
end


lemma Trigo_5_385_SWHN_extend(h0 : tan(pi/9) ≠ 0) (h1 : sin(pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0)  (h3 : tan(pi/9)≠ 0) (h4 : tan(712*pi/9)≠ 0) : -2*cos(2*pi/9) - sqrt(3)*cos(-203*pi/9)*tan(7*pi/18) + cos(pi/18)/tan(712*pi/9)=2:=
begin
have : (-2) * cos(2 * pi / 9) - sqrt 3 * cos((-203) * pi / 9) * tan(7 * pi / 18) + cos(pi / 18) / tan(712 * pi / 9) = -2*cos(2*pi/9) - sqrt(3)*cos(-203*pi/9)*tan(7*pi/18) + cos(pi/18)/tan(712*pi/9),
{
field_simp at *,
},
have : tan(pi/9) = tan(712*pi/9),
{
rw tan_eq_tan_add_int_mul_pi (pi/9) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-2) * cos(2 * pi / 9) + sqrt 3 * -cos((-203) * pi / 9) * tan(7 * pi / 18) + cos(pi / 18) / tan(pi / 9) = -2*cos(2*pi/9) - sqrt(3)*cos(-203*pi/9)*tan(7*pi/18) + cos(pi/18)/tan(pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1189*pi/18) = -cos(-203*pi/9),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (1189*pi/18) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(1189 * pi / 18) * tan(7 * pi / 18) + cos(pi / 18) / tan(pi / 9) - 2 * cos(2 * pi / 9) = -2*cos(2*pi/9) + sqrt(3)*sin(1189*pi/18)*tan(7*pi/18) + cos(pi/18)/tan(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = sin(1189*pi/18),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/18) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/18) = 1/tan(pi/9),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sqrt(3)*sin(pi/18)*(1/tan(pi/9)) + cos(pi/18)/tan(pi/9) = (sqrt(3)*sin(pi/18) + cos(pi/18))/tan(pi/9),
{
ring_exp,
},
rw this,
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
rw tan_eq_sin_div_cos,
have : 2*cos(2*pi/9) = 2*cos(pi/9)**2 - 2*sin(pi/9)**2,
{
have : cos(2*pi/9) = -sin(pi/9)**2 + cos(pi/9)**2,
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
linarith,
},
rw this,
have : 2*(2*sin(pi/9)*cos(pi/9))/(sin(pi/9)/cos(pi/9)) = 4*cos(pi/9)**2,
{
field_simp,
ring_exp,
},
rw this,
ring_exp,
have : sin(pi/9)**2 + cos(pi/9)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
end


lemma Trigo_5_386_TYJS_extend(h0 : 2 ≠ 0)  : -(-4*sin(x/3)**3 + 3*sin(x/3))*cos(-x + pi/6) - cos(x)**2 + cos(-2*x + pi/3)/2 + 3/2=3/4:=
begin
have : -((-4) * sin(x / 3) ** 3 + 3 * sin(x / 3)) * cos(-x + pi / 6) - cos(x) ** 2 + cos((-2) * x + pi / 3) / 2 + 3 / 2 = -(-4*sin(x/3)**3 + 3*sin(x/3))*cos(-x + pi/6) - cos(x)**2 + cos(-2*x + pi/3)/2 + 3/2,
{
field_simp at *,
},
have : sin(x) = -4 * sin(x/3) ** 3 + 3 * sin(x/3),
{
have : sin(x) = sin(3*(x/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(x) ** 2 - sin(x) * cos(-x + pi / 6) + cos((-2) * x + pi / 3) / 2 + 1 / 2 = -sin(x)*cos(-x + pi/6) - cos(x)**2 + cos(-2*x + pi/3)/2 + 3/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) ** 2 = 1 - cos(x) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : sin(x) ** 2 - sin(x) * cos(-x + pi / 6) + (cos((-2) * x + pi / 3) / 2 + 1 / 2) = sin(x)**2 - sin(x)*cos(-x + pi/6) + cos(-2*x + pi/3)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + pi/6) ** 2 = cos(-2*x + pi/3) / 2 + 1 / 2,
{
have : cos(-2*x + pi/3) = cos(2*(-x + pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + pi/6) = sin(pi/6)*sin(x) + cos(pi/6)*cos(x),
{
have : cos(-x+pi/6) = cos((pi/6) - (x)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw this,
have : (sin(pi/6)*sin(x) + cos(pi/6)*cos(x))**2 = sin(pi/6)**2*sin(x)**2 + 2*sin(pi/6)*sin(x)*cos(pi/6)*cos(x) + cos(pi/6)**2*cos(x)**2,
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw sin_pi_div_six,
rw cos_pi_div_six,
have : sin(x)*(1/2*sin(x) + sqrt(3)/2*cos(x)) = sin(x)**2/2 + sqrt(3)*sin(x)*cos(x)/2,
{
ring_exp,
},
rw this,
ring_nf,
rw sq_sqrt,
have : sin(x)**2 + cos(x)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
repeat {linarith},
end


lemma Trigo_5_387_DCTK_extend : -(-3*cos(4*pi/15) + 4*cos(4*pi/15)**3)*cos(2422*pi/15) + sin(726*pi/5)*cos(29*pi/30)=1/2:=
begin
have : -(4 * cos(4 * pi / 15) ** 3 - 3 * cos(4 * pi / 15)) * cos(2422 * pi / 15) + sin(726 * pi / 5) * cos(29 * pi / 30) = -(-3*cos(4*pi/15) + 4*cos(4*pi/15)**3)*cos(2422*pi/15) + sin(726*pi/5)*cos(29*pi/30),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/5) = 4 * cos(4*pi/15) ** 3 - 3 * cos(4*pi/15),
{
have : cos(4*pi/5) = cos(3*(4*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : -cos(4 * pi / 5) * cos(2422 * pi / 15) - -sin(726 * pi / 5) * cos(29 * pi / 30) = -cos(4*pi/5)*cos(2422*pi/15) + sin(726*pi/5)*cos(29*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/5) = -sin(726*pi/5),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (4*pi/5) (73),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(4 * pi / 5) * cos(29 * pi / 30) + -cos(2422 * pi / 15) * cos(4 * pi / 5) = -cos(4*pi/5)*cos(2422*pi/15) - sin(4*pi/5)*cos(29*pi/30),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(29*pi/30) = -cos(2422*pi/15),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (29*pi/30) (80),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(4*pi/5)*cos(29*pi/30) + sin(29*pi/30)*cos(4*pi/5) = sin(pi/6),
{
have : sin(pi/6) = sin((29*pi/30) - (4*pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw sin_pi_div_six,
end


lemma Trigo_5_388_APKQ_extend (h0 : cos(13*pi/180)≠ 0) (h1 : (2*cos(13*pi/180))≠ 0) : cos(13*pi/180)*cos(25427*pi/180) + (-sin(-2*pi)*sin(403*pi/180) + cos(-2*pi)*cos(403*pi/180))*sin(13*pi/90)/(2*cos(13*pi/180))=-1/2:=
begin
have : - -cos(25427 * pi / 180) * cos(13 * pi / 180) + (-sin((-2) * pi) * sin(403 * pi / 180) + cos((-2) * pi) * cos(403 * pi / 180)) * sin(13 * pi / 90) / (2 * cos(13 * pi / 180)) = cos(13*pi/180)*cos(25427*pi/180) + (-sin(-2*pi)*sin(403*pi/180) + cos(-2*pi)*cos(403*pi/180))*sin(13*pi/90)/(2*cos(13*pi/180)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(43*pi/180) = -cos(25427*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (43*pi/180) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(43 * pi / 180) * cos(13 * pi / 180) + sin(13 * pi / 90) * (-sin(403 * pi / 180) * sin((-2) * pi) + cos(403 * pi / 180) * cos((-2) * pi)) / (2 * cos(13 * pi / 180)) = -sin(43*pi/180)*cos(13*pi/180) + (-sin(-2*pi)*sin(403*pi/180) + cos(-2*pi)*cos(403*pi/180))*sin(13*pi/90)/(2*cos(13*pi/180)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(43*pi/180) = -sin(403*pi/180) * sin(-2*pi) + cos(403*pi/180) * cos(-2*pi),
{
have : cos(43*pi/180) = cos((403*pi/180) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13 * pi / 90) / (2 * cos(13 * pi / 180)) * cos(43 * pi / 180) - sin(43 * pi / 180) * cos(13 * pi / 180) = -sin(43*pi/180)*cos(13*pi/180) + sin(13*pi/90)*cos(43*pi/180)/(2*cos(13*pi/180)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = sin(13*pi/90) / ( 2 * cos(13*pi/180) ),
{
have : sin(13*pi/90) = sin(2*(13*pi/180)),
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
rw sub_eq_neg_add,
rw ← neg_mul,
have : -sin(43*pi/180)*cos(13*pi/180) + sin(13*pi/180)*cos(43*pi/180) = sin(-pi/6),
{
have : sin(-pi/6) = sin((13*pi/180) - (43*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
have : sin(-pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
end


lemma Trigo_5_389_KLXX_extend(h0 : cos(pi/5) ≠ 0) (h1 : cos(2*pi/15) ≠ 0) (h2 : 1 - tan(pi/5) * tan(2*pi/15) ≠ 0)  (h3 : tan(251*pi/30)≠ 0) (h4 : (sin(251*pi/30)/cos(251*pi/30))≠ 0) (h5 : sin(251*pi/30)≠ 0) (h6 : cos(251*pi/30)≠ 0) (h7 : cos(332*pi/15)≠ 0) : cos(251*pi/30)/cos(332*pi/15) + sqrt(3)*cos(251*pi/30)*tan(pi/5)/cos(332*pi/15) + tan(pi/5)=sqrt(3):=
begin
have : cos(251 * pi / 30) / cos(332 * pi / 15) + sqrt 3 * cos(251 * pi / 30) * tan(pi / 5) / cos(332 * pi / 15) + tan(pi / 5) = cos(251*pi/30)/cos(332*pi/15) + sqrt(3)*cos(251*pi/30)*tan(pi/5)/cos(332*pi/15) + tan(pi/5),
{
field_simp at *,
},
have : sin(251*pi/30) = cos(332*pi/15),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (251*pi/30) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 / (sin(251 * pi / 30) / cos(251 * pi / 30)) + sqrt 3 * tan(pi / 5) / (sin(251 * pi / 30) / cos(251 * pi / 30)) + tan(pi / 5) = cos(251*pi/30)/sin(251*pi/30) + sqrt(3)*cos(251*pi/30)*tan(pi/5)/sin(251*pi/30) + tan(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(251*pi/30) = sin(251*pi/30) / cos(251*pi/30),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * (1 / tan(251 * pi / 30)) * tan(pi / 5) + 1 / tan(251 * pi / 30) + tan(pi / 5) = 1/tan(251*pi/30) + sqrt(3)*tan(pi/5)/tan(251*pi/30) + tan(pi/5),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2*pi/15) = 1 / tan(251*pi/30),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (2*pi/15) (8),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(2*pi/15) + tan(pi/5) = (-tan(2*pi/15)*tan(pi/5) + 1)*tan(pi/3),
{
rw add_comm,
rw tan_add_tan,
have : tan((pi/5) + (2*pi/15)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(2*pi/15)*tan(pi/5) + 1)*tan(pi/3) = -tan(2*pi/15)*tan(pi/5)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
norm_num,
ring_exp,
end


lemma Trigo_5_390_CVUX_extend(h0 : sin(5*pi/18) ≥ 0) (h1 : cos(5*pi/18) ≥ 0)  : -sqrt(-2*sin(1835*pi/36)*cos(1835*pi/36) + 1) + sqrt(2*sin(1835*pi/36)*cos(1835*pi/36) + 1)=-2*sin(pi/36):=
begin
have : -sqrt (1 - 2 * sin(1835 * pi / 36) * cos(1835 * pi / 36)) + sqrt (2 * sin(1835 * pi / 36) * cos(1835 * pi / 36) + 1) = -sqrt(-2*sin(1835*pi/36)*cos(1835*pi/36) + 1) + sqrt(2*sin(1835*pi/36)*cos(1835*pi/36) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1835*pi/18) = 2 * sin(1835*pi/36) * cos(1835*pi/36),
{
have : sin(1835*pi/18) = sin(2*(1835*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
conv {to_lhs, rw ← this,},
have : cos(275*pi/9) = sin(1835*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (275*pi/9) (66),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/9) = cos(275*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (5*pi/9) (15),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/9) = -sin(5*pi/18)**2 + cos(5*pi/18)**2,
{
have : cos(5*pi/9) = cos(2*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
have : 1 - (-sin(5*pi/18)**2 + cos(5*pi/18)**2) = (sin(5*pi/18)**2 + cos(5*pi/18)**2) - (-sin(5*pi/18)**2 + cos(5*pi/18)**2),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : (sin(5*pi/18)**2 + cos(5*pi/18)**2) - (-sin(5*pi/18)**2 + cos(5*pi/18)**2) = 2*sin(5*pi/18)**2,
{
ring,
},
rw this,
rw sqrt_mul,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
rw sin_sq,
have : -(1-cos(5*pi/18)**2) + cos(5*pi/18)**2 + 1 = 2*cos(5*pi/18)**2,
{
ring,
},
rw this,
rw sqrt_mul,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h1,
have : sin(5*pi/18) = sqrt(2)*cos(pi/4)*sin(5*pi/18),
{
field_simp,
},
rw this,
have : cos(5*pi/18) = sqrt(2)*sin(pi/4)*cos(5*pi/18),
{
field_simp,
},
rw this,
ring_exp,
rw sq_sqrt,
have : 2*(cos(pi/4)*-sin(5*pi/18)) + 2*(sin(pi/4)*cos(5*pi/18)) = -2*sin(5*pi/18)*cos(pi/4) + 2*sin(pi/4)*cos(5*pi/18),
{
ring,
},
rw this,
have : -2*sin(5*pi/18)*cos(pi/4) + 2*sin(pi/4)*cos(5*pi/18) = 2*sin(-pi/36),
{
have : sin(-pi/36) = sin(pi/4)*cos(5*pi/18) - sin(5*pi/18)*cos(pi/4),
{
have : sin(-pi/36) = sin((pi/4) - (5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : sin(-pi/36) = -sin(pi/36),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
ring_exp,
repeat {linarith},
end


lemma Trigo_5_391_NULQ_extend(h0 : cos(pi/180) ≠ 0) (h1 : cos(11*pi/45) ≠ 0) (h2 : 1 - tan(pi/180) * tan(11*pi/45) ≠ 0)  (h3 : tan(15751*pi/180)≠ 0) (h4 : cos(11*pi/45)≠ 0) (h5 : (cos(-pi/2)*cos(-23*pi/90)+sin(-pi/2)*sin(-23*pi/90))≠ 0) (h6 : (sin((-23)*pi/90)*sin(-pi/2)+cos((-23)*pi/90)*cos(-pi/2))≠ 0) : (1 - 1/tan(15751*pi/180))*(sin(11*pi/45)/(cos(-pi/2)*cos(-23*pi/90) + sin(-pi/2)*sin(-23*pi/90)) + 1)=2:=
begin
have : (1 - 1 / tan(15751 * pi / 180)) * (sin(11 * pi / 45) / (sin((-23) * pi / 90) * sin(-pi / 2) + cos((-23) * pi / 90) * cos(-pi / 2)) + 1) = (1 - 1/tan(15751*pi/180))*(sin(11*pi/45)/(cos(-pi/2)*cos(-23*pi/90) + sin(-pi/2)*sin(-23*pi/90)) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(11*pi/45) = sin(-23*pi/90) * sin(-pi/2) + cos(-23*pi/90) * cos(-pi/2),
{
have : cos(11*pi/45) = cos((-23*pi/90) - (-pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/45) = sin(11*pi/45) / cos(11*pi/45),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : ((-1) / tan(15751 * pi / 180) + 1) * (tan(11 * pi / 45) + 1) = (1 - 1/tan(15751*pi/180))*(tan(11*pi/45) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/180) = -1 / tan(15751*pi/180),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (pi/180) (87),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi/180) + 1)*(tan(11*pi/45) + 1) = tan(pi/180)*tan(11*pi/45) + tan(pi/180) + tan(11*pi/45) + 1,
{
ring_exp,
},
rw this,
have : tan(pi/180)*tan(11*pi/45) + tan(pi/180) + tan(11*pi/45) = tan(pi/180)*tan(11*pi/45) + (tan(pi/180) + tan(11*pi/45)),
{
ring,
},
rw this,
have : tan(pi/180) + tan(11*pi/45) = (-tan(pi/180)*tan(11*pi/45) + 1)*tan(pi/4),
{
rw tan_add_tan,
have : tan((pi/180) + (11*pi/45)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
norm_num,
end


lemma Trigo_5_392_ZNUK_extend(h0 : 1 - tan(pi/10) * tan(7*pi/30) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : cos(7*pi/30) ≠ 0)  (h3 : cos(pi/10)≠ 0) (h4 : cos(7*pi/30)≠ 0) (h5 : 1 - tan(pi/10) * tan(7*pi/30)≠ 0) (h6 : cos((2*pi/3)/2)≠ 0) (h7 : (1+cos(2*pi/3))≠ 0) (h8 : (cos(2*pi/3)+1)≠ 0) : sqrt(3)*tan(pi/10)*tan(7*pi/30) + (-tan(pi/10)*tan(7*pi/30) + 1)*sin(379*pi/3)/(cos(2*pi/3) + 1)=sqrt(3):=
begin
have : sqrt 3 * tan(pi / 10) * tan(7 * pi / 30) + (-tan(pi / 10) * tan(7 * pi / 30) + 1) * sin(379 * pi / 3) / (cos(2 * pi / 3) + 1) = sqrt(3)*tan(pi/10)*tan(7*pi/30) + (-tan(pi/10)*tan(7*pi/30) + 1)*sin(379*pi/3)/(cos(2*pi/3) + 1),
{
field_simp at *,
},
have : sin(2*pi/3) = sin(379*pi/3),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (63),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * tan(pi / 10) * tan(7 * pi / 30) + (-tan(pi / 10) * tan(7 * pi / 30) + 1) * (sin(2 * pi / 3) / (1 + cos(2 * pi / 3))) = sqrt(3)*tan(pi/10)*tan(7*pi/30) + (-tan(pi/10)*tan(7*pi/30) + 1)*sin(2*pi/3)/(cos(2*pi/3) + 1),
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
have : (-tan(pi / 10) * tan(7 * pi / 30) + 1) * tan(pi / 3) + sqrt 3 * tan(pi / 10) * tan(7 * pi / 30) = sqrt(3)*tan(pi/10)*tan(7*pi/30) + (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) + tan(7*pi/30) = ( -tan(pi/10) * tan(7*pi/30) + 1 ) * tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/10) + (7*pi/30)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(pi/10) + tan(7*pi/30)) + sqrt(3)*tan(pi/10)*tan(7*pi/30) = sqrt(3)*tan(pi/10)*tan(7*pi/30)+tan(pi/10)+tan(7*pi/30),
{
ring,
},
conv {to_lhs, rw this,},
rw add_assoc,
have : tan(pi/10) + tan(7*pi/30) = (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/10) + (7*pi/30)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3) = -tan(pi/10)*tan(7*pi/30)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
norm_num,
ring_exp,
end


lemma Trigo_5_393_MLNR_extend(h0 : 1+tan(pi/9)*tan(5*pi/18) ≠ 0) (h1 : cos(5*pi/18) ≠ 0) (h2 : tan((pi/9)-(5*pi/18)) ≠ 0) (h3 : cos(pi/9) ≠ 0) (h4 : cos(5*pi/18) ≠ 0) (h5 : tan(pi/9) - tan(5*pi/18) ≠ 0) (h6 : sqrt(3) ≠ 0)  (h7 : cos(pi/9)≠ 0) (h8 : (-tan(5*pi/18)+sin(pi/9)/cos(pi/9))≠ 0) (h9 : (sin(pi/9)/cos(pi/9)-tan(5*pi/18))≠ 0) (h10 : cos(pi/18)≠ 0) (h11 : cos(pi/3)≠ 0) (h12 : ((tan(pi/18)*tan(pi/3)+1)*cos(pi/9))≠ 0) (h13 : (1+tan(pi/18)*tan(pi/3))≠ 0) (h14 : (-tan(5*pi/18)+sin(73*pi/9)/cos(pi/9))≠ 0) : (-1 + (-tan(pi/3) + tan(pi/18))*sin(73*pi/9)/((tan(pi/18)*tan(pi/3) + 1)*cos(pi/9)))/(-tan(5*pi/18) + sin(73*pi/9)/cos(pi/9))=sqrt(3):=
begin
have : sin(pi/9) = sin(73*pi/9),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/9) (4),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-1 + sin(pi / 9) * ((tan(pi / 18) - tan(pi / 3)) / (1 + tan(pi / 18) * tan(pi / 3))) / cos(pi / 9)) / (-tan(5 * pi / 18) + sin(pi / 9) / cos(pi / 9)) = (-1 + (-tan(pi/3) + tan(pi/18))*sin(pi/9)/((tan(pi/18)*tan(pi/3) + 1)*cos(pi/9)))/(-tan(5*pi/18) + sin(pi/9)/cos(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(-5*pi/18) = ( tan(pi/18) - tan(pi/3) ) / ( 1 + tan(pi/18) * tan(pi/3) ),
{
have : tan(-5*pi/18) = tan((pi/18) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_sub,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan((-5) * pi / 18) * (sin(pi / 9) / cos(pi / 9)) - 1) / (sin(pi / 9) / cos(pi / 9) - tan(5 * pi / 18)) = (-1 + sin(pi/9)*tan(-5*pi/18)/cos(pi/9))/(-tan(5*pi/18) + sin(pi/9)/cos(pi/9)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = sin(pi/9) / cos(pi/9),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : tan(-5*pi/18) = -tan(5*pi/18),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw neg_mul,
rw mul_comm,
have : tan(pi/9)*tan(5*pi/18) = -1 + (-tan(5*pi/18) + tan(pi/9))/tan(-pi/6),
{
rw tan_mul_tan,
have : tan((pi/9) - (5*pi/18)) = tan(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : tan(-pi/6) = -tan(pi/6),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_pi_div_six,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_5_394_RKYM_extend : 5*(2*cos(x/2)**2 - 1)**4 - (2*cos(x/2)**2 - 1)*sin(-3*x + 281*pi/2) + 2*sin(x)**4 + 3*sin(2*x)**2/4=2*(1+cos(x)**2):=
begin
have : 5 * (1 - 2 * (1 - cos(x / 2) ** 2)) ** 4 - (1 - 2 * (1 - cos(x / 2) ** 2)) * sin((-3) * x + 281 * pi / 2) + 2 * sin(x) ** 4 + 3 * sin(2 * x) ** 2 / 4 = 5*(2*cos(x/2)**2 - 1)**4 - (2*cos(x/2)**2 - 1)*sin(-3*x + 281*pi/2) + 2*sin(x)**4 + 3*sin(2*x)**2/4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x/2) ** 2 = 1 - cos(x/2) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(x) ** 4 + 3 * sin(2 * x) ** 2 / 4 - sin((-3) * x + 281 * pi / 2) * (1 - 2 * sin(x / 2) ** 2) + 5 * (1 - 2 * sin(x / 2) ** 2) ** 4 = 5*(1 - 2*sin(x/2)**2)**4 - (1 - 2*sin(x/2)**2)*sin(-3*x + 281*pi/2) + 2*sin(x)**4 + 3*sin(2*x)**2/4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = 1 - 2 * sin(x/2) ** 2,
{
have : cos(x) = cos(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : 2 * sin(x) ** 4 + 3 * sin(2 * x) ** 2 / 4 + 5 * cos(x) ** 4 - cos(x) * sin((-3) * x + 281 * pi / 2) = 2*sin(x)**4 + 3*sin(2*x)**2/4 - sin(-3*x + 281*pi/2)*cos(x) + 5*cos(x)**4,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(3*x) = sin(-3*x + 281*pi/2),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (3*x) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
have : cos(3*x) = 4*cos(x)**3 - 3*cos(x),
{
have : cos(3*x) = cos(3*(x)),
{
apply congr_arg,
ring,
},
rw cos_three_mul,
},
rw this,
have : cos(x)*(4*cos(x)**3 - 3*cos(x)) = 4*cos(x)**4 - 3*cos(x)**2,
{
ring_exp,
},
rw this,
have : 2*sin(x)**4 + 3*(2*sin(x)*cos(x))**2/4 + 5*cos(x)**4 - (4*cos(x)**4 - 3*cos(x)**2) = 2*sin(x)**4 + 3*sin(x)**2*cos(x)**2 + cos(x)**4 + 3*cos(x)**2,
{
ring,
},
rw this,
have : 2*sin(x)**4 + 3*sin(x)**2*cos(x)**2 + cos(x)**4 = (sin(x)**2 + cos(x)**2)*(2*sin(x)**2 + cos(x)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
ring_exp,
rw sin_sq,
ring_exp,
end


lemma Trigo_5_395_KSOQ_extend(h0 : sin(pi/9) ≠ 0)  (h1 : cos(5*pi/18)≠ 0) (h2 : (2*cos(5*pi/18))≠ 0) : -sin(pi/18)*sin(5*pi/9)*sin(389*pi/6)*sin(3553*pi/18)/(2*cos(5*pi/18))=1/16:=
begin
have : sin(pi / 18) * -sin(3553 * pi / 18) * sin(5 * pi / 9) * sin(389 * pi / 6) / (2 * cos(5 * pi / 18)) = -sin(pi/18)*sin(5*pi/9)*sin(389*pi/6)*sin(3553*pi/18)/(2*cos(5*pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = -sin(3553*pi/18),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/18) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 18) * (sin(5 * pi / 9) / (2 * cos(5 * pi / 18))) * sin(7 * pi / 18) * sin(389 * pi / 6) = sin(pi/18)*sin(7*pi/18)*sin(5*pi/9)*sin(389*pi/6)/(2*cos(5*pi/18)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5*pi/18) = sin(5*pi/9) / ( 2 * cos(5*pi/18) ),
{
have : sin(5*pi/9) = sin(2*(5*pi/18)),
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
have : sin(pi / 18) * sin(389 * pi / 6) * sin(5 * pi / 18) * sin(7 * pi / 18) = sin(pi/18)*sin(5*pi/18)*sin(7*pi/18)*sin(389*pi/6),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/6) = sin(389*pi/6),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/6) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = cos(4*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(5*pi/18) = cos(2*pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/18) = cos(pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : cos(4*pi/9)*sin(pi/6)*cos(2*pi/9)*(sin(2*pi/9)/(2*sin(pi/9))) = sin(2*pi/9)*cos(2*pi/9)*cos(4*pi/9)*sin(pi/6)/(2*sin(pi/9)),
{
ring,
},
rw this,
have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
{
have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(4*pi/9)/2*cos(4*pi/9) = sin(4*pi/9)*cos(4*pi/9)/2,
{
ring,
},
rw this,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
field_simp,
ring_exp,
end


lemma Trigo_5_396_SLLC_extend (h0 : cos(2*pi/9)≠ 0) (h1 : (4*cos(2*pi/9)**2)≠ 0) (h2 : (2*cos(2*pi/9))≠ 0) : -sin(845*pi/6)/2 + sin(pi/9)**2 + sin(4*pi/9)**2/(4*cos(2*pi/9)**2) - sin(-2531*pi/18)/2=3/4:=
begin
have : -sin(845 * pi / 6) / 2 + sin(pi / 9) ** 2 + (sin(4 * pi / 9) / (2 * cos(2 * pi / 9))) ** 2 - sin((-2531) * pi / 18) / 2 = -sin(845*pi/6)/2 + sin(pi/9)**2 + sin(4*pi/9)**2/(4*cos(2*pi/9)**2) - sin(-2531*pi/18)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*pi/9) = sin(4*pi/9) / ( 2 * cos(2*pi/9) ),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
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
have : sin(pi / 9) ** 2 - (sin((-2531) * pi / 18) / 2 + sin(845 * pi / 6) / 2) + sin(2 * pi / 9) ** 2 = -sin(845*pi/6)/2 + sin(pi/9)**2 + sin(2*pi/9)**2 - sin(-2531*pi/18)/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) * cos(2533*pi/18) = sin(-2531*pi/18) / 2 + sin(845*pi/6) / 2,
{
rw sin_mul_cos,
have : sin((pi/9) + (2533*pi/18)) = sin(845*pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/9) - (2533*pi/18)) = sin(-2531*pi/18),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (sin(pi/9) * cos(2533*pi/18)) = sin(pi/9)*cos(2533*pi/18),
{
ring,
},
have : sin(pi / 9) ** 2 + sin(pi / 9) * -cos(2533 * pi / 18) + sin(2 * pi / 9) ** 2 = sin(pi/9)**2 - sin(pi/9)*cos(2533*pi/18) + sin(2*pi/9)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(5*pi/18) = -cos(2533*pi/18),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/18) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9)**2 = 1/2 - cos(2*pi/9)/2,
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
have : sin(2*pi/9)**2 = 1/2 - cos(4*pi/9)/2,
{
have : cos(4*pi/9) = cos(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : 1/2 - cos(2*pi/9)/2 + sin(pi/9)*cos(5*pi/18) + (1/2 - cos(4*pi/9)/2) = -cos(2*pi/9)/2 - cos(4*pi/9)/2 + sin(pi/9)*cos(5*pi/18) + 1,
{
ring,
},
rw this,
have : -cos(2*pi/9)/2 - cos(4*pi/9)/2 = -cos(pi/9)*cos(pi/3),
{
have : cos(2*pi/9) + cos(4*pi/9) = 2*cos(pi/9)*cos(pi/3),
{
rw add_comm,
rw cos_add_cos,
have : cos(((4*pi/9) + (2*pi/9))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((4*pi/9) - (2*pi/9))/2) = cos(pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
have : sin(pi/9)*cos(5*pi/18) = sin(-pi/6)/2 + sin(7*pi/18)/2,
{
rw sin_mul_cos,
have : sin((pi/9) + (5*pi/18)) = sin(7*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : sin((pi/9) - (5*pi/18)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(-pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/6) = cos(pi/3),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(7*pi/18) = cos(pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_5_397_YLLO_extend(h0 : -cos(pi/18) + sin(pi/18) ≤ 0) (h1 : -sin(π/18) + cos(π/18) ≠ 0) (h2 : sin(11*pi/36) ≠ 0)  (h3 : (sqrt(1-2*sin(pi/18)*cos(pi/18))*cos(7*pi/36))≠ 0) (h4 : (sqrt(-2*sin(pi/18)*cos(pi/18)+1)*cos(7*pi/36))≠ 0) (h5 : sin(7*pi/36)≠ 0) (h6 : (sqrt((-2)*sin(pi/18)*cos(pi/18)+1)*(sin(7*pi/18)/(2*sin(7*pi/36))))≠ 0) (h7 : (sqrt(-2*sin(pi/18)*cos(pi/18)+1)*sin(7*pi/18))≠ 0) (h8 : (2*sin(7*pi/36))≠ 0) (h9 : (sqrt((-2)*sin(pi/18)*cos(pi/18)+1)*sin(7*pi/18))≠ 0) : -2*sin(7*pi/36)*sin(853*pi/18)/(sqrt(-2*sin(pi/18)*cos(pi/18) + 1)*sin(7*pi/18))=sqrt(2):=
begin
have : 2 * sin(7 * pi / 36) * -sin(853 * pi / 18) / (sqrt ((-2) * sin(pi / 18) * cos(pi / 18) + 1) * sin(7 * pi / 18)) = -2*sin(7*pi/36)*sin(853*pi/18)/(sqrt(-2*sin(pi/18)*cos(pi/18) + 1)*sin(7*pi/18)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -sin(853*pi/18),
{
rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/9) (23),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi / 9) / (sqrt ((-2) * sin(pi / 18) * cos(pi / 18) + 1) * (sin(7 * pi / 18) / (2 * sin(7 * pi / 36)))) = 2*sin(7*pi/36)*cos(pi/9)/(sqrt(-2*sin(pi/18)*cos(pi/18) + 1)*sin(7*pi/18)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(7*pi/36) = sin(7*pi/18) / ( 2 * sin(7*pi/36) ),
{
have : sin(7*pi/18) = sin(2*(7*pi/36)),
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
have : cos(pi / 9) / (sqrt (1 - 2 * sin(pi / 18) * cos(pi / 18)) * cos(7 * pi / 36)) = cos(pi/9)/(sqrt(-2*sin(pi/18)*cos(pi/18) + 1)*cos(7*pi/36)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
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
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : 1 - 2*sin(pi/18)*cos(pi/18) = sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(pi/18)*cos(pi/18),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(pi/18)*cos(pi/18) = (-cos(pi/18) + sin(pi/18))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_neg_self.mpr h0,
have : cos(pi/9) = -sin(pi/18)**2 + cos(pi/18)**2,
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
rw this,
have : -sin(pi/18)**2 + cos(pi/18)**2 = (-sin(pi/18) + cos(pi/18))*(sin(pi/18) + cos(pi/18)),
{
ring_exp,
},
rw this,
have : sin(pi/18) + cos(pi/18) = sqrt(2)*(sqrt(2)*sin(pi/18)/2 + sqrt(2)*cos(pi/18)/2),
{
ring_exp,
rw sq_sqrt,
have : pi*(1/18) = pi/18,
{
ring,
},
rw this,
ring_exp,
linarith,
},
rw this,
have : sqrt(2)*sin(pi/18)/2 = sin(pi/18)*cos(pi/4),
{
field_simp,
ring_exp,
},
rw this,
have : sqrt(2)*cos(pi/18)/2 = sin(pi/4)*cos(pi/18),
{
field_simp,
},
rw this,
have : sin(pi/18)*cos(pi/4) + sin(pi/4)*cos(pi/18) = sin(11*pi/36),
{
have : sin(11*pi/36) = sin((pi/4) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
have : cos(7*pi/36) = sin(11*pi/36),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_5_398_VGEE_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : sin(x + 3*pi/2)≠ 0) (h3 : (sin(-x)*sin(2*x+3*pi))≠ 0) (h4 : (sin(-x)*(sin(2*x+3*pi)/(2*sin(x+3*pi/2))))≠ 0) (h5 : (2*sin(x+3*pi/2))≠ 0) (h6 : (sin(-x)*cos((-2)*x+135*pi/2))≠ 0) (h7 : (sin(-x)*cos(-2*x+135*pi/2))≠ 0) (h8 : (sin(-x)*cos(2*x-51*pi/2))≠ 0) : 2*sin(x + pi/2)*sin(x + pi)*sin(x + 3*pi/2)*tan(x + 3*pi)/(sin(-x)*cos(2*x - 51*pi/2))=1:=
begin
have : cos(-2*x + 135*pi/2) = cos(2*x - 51*pi/2),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-2*x + 135*pi/2) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(x + pi / 2) * sin(x + pi) * sin(x + 3 * pi / 2) * tan(x + 3 * pi) / (sin(-x) * cos((-2) * x + 135 * pi / 2)) = 2*sin(x + pi/2)*sin(x + pi)*sin(x + 3*pi/2)*tan(x + 3*pi)/(sin(-x)*cos(-2*x + 135*pi/2)),
{
field_simp at *,
},
have : sin(2*x + 3*pi) = cos(-2*x + 135*pi/2),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (2*x + 3*pi) (35),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + pi / 2) * sin(x + pi) * tan(x + 3 * pi) / (sin(-x) * (sin(2 * x + 3 * pi) / (2 * sin(x + 3 * pi / 2)))) = 2*sin(x + pi/2)*sin(x + pi)*sin(x + 3*pi/2)*tan(x + 3*pi)/(sin(-x)*sin(2*x + 3*pi)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + 3*pi/2) = sin(2*x + 3*pi) / ( 2 * sin(x + 3*pi/2) ),
{
have : sin(2*x + 3*pi) = sin(2*(x + 3*pi/2)),
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
have : sin(x + pi/2) = cos(x),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(x + pi) = -sin(x),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : tan(x + 3*pi) = tan(x),
{
rw tan_eq_tan_add_int_mul_pi (x + 3*pi) (-3),
repeat {apply congr_arg _},
simp,
},
rw this,
have : sin(-x) = -sin(x),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x) (0),
repeat {apply congr_arg _},
simp,
},
rw this,
have : cos(x + 3*pi/2) = sin(x),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x + 3*pi/2) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_5_399_NEPM_extend(h0 : cos(x) ≠ 0) (h1 : 1 - cos(x)**2 ≠ 0) (h2 : (-(sin(x+pi)*cos(pi)-sin(pi)*cos(x+pi))**4+(sin(x+pi)*cos(pi)-sin(pi)*cos(x+pi))**2)≠ 0) (h3 : (-(sin(x+pi)*cos(pi)-sin(pi)*-sin(x+189*pi/2))**4+(sin(x+pi)*cos(pi)-sin(pi)*-sin(x+189*pi/2))**2)≠ 0) (h4 : (-(sin(x+pi)*cos(pi)+sin(pi)*sin(x+189*pi/2))**4+(sin(x+pi)*cos(pi)+sin(pi)*sin(x+189*pi/2))**2)≠ 0) (h5 : (-(sin(x+pi)*sin(163*pi/2)+sin(pi)*sin(x+189*pi/2))**4+(sin(x+pi)*sin(163*pi/2)+sin(pi)*sin(x+189*pi/2))**2)≠ 0) (h6 : (-(sin(163*pi/2)*sin(x+pi)+sin(pi)*sin(x+189*pi/2))**4+(sin(163*pi/2)*sin(x+pi)+sin(pi)*sin(x+189*pi/2))**2)≠ 0) : (-(sin(163*pi/2)*sin(x + pi) + sin(pi)*sin(x + 189*pi/2))**4 - cos(x)**4 + 1)/(-(sin(163*pi/2)*sin(x + pi) + sin(pi)*sin(x + 189*pi/2))**4 + (sin(163*pi/2)*sin(x + pi) + sin(pi)*sin(x + 189*pi/2))**2)=2:=
begin
have : (-(sin(x + pi) * sin(163 * pi / 2) + sin(pi) * sin(x + 189 * pi / 2)) ** 4 - cos(x) ** 4 + 1) / (-(sin(x + pi) * sin(163 * pi / 2) + sin(pi) * sin(x + 189 * pi / 2)) ** 4 + (sin(x + pi) * sin(163 * pi / 2) + sin(pi) * sin(x + 189 * pi / 2)) ** 2) = (-(sin(163*pi/2)*sin(x + pi) + sin(pi)*sin(x + 189*pi/2))**4 - cos(x)**4 + 1)/(-(sin(163*pi/2)*sin(x + pi) + sin(pi)*sin(x + 189*pi/2))**4 + (sin(163*pi/2)*sin(x + pi) + sin(pi)*sin(x + 189*pi/2))**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi) = sin(163*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi) (40),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-(sin(x + pi) * cos(pi) - sin(pi) * -sin(x + 189 * pi / 2)) ** 4 - cos(x) ** 4 + 1) / (-(sin(x + pi) * cos(pi) - sin(pi) * -sin(x + 189 * pi / 2)) ** 4 + (sin(x + pi) * cos(pi) - sin(pi) * -sin(x + 189 * pi / 2)) ** 2) = (-(sin(x + pi)*cos(pi) + sin(pi)*sin(x + 189*pi/2))**4 - cos(x)**4 + 1)/(-(sin(x + pi)*cos(pi) + sin(pi)*sin(x + 189*pi/2))**4 + (sin(x + pi)*cos(pi) + sin(pi)*sin(x + 189*pi/2))**2),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(x + pi) = -sin(x + 189*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi) (46),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = sin(x + pi) * cos(pi) - sin(pi) * cos(x + pi),
{
have : sin(x) = sin((x + pi) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x)**4 - cos(x)**4 = (-sin(x)**2 - cos(x)**2)*(sin(x)**2 + cos(x)**2) + 2*sin(x)**2*cos(x)**2,
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : -sin(x)**2 - cos(x)**2 = -1,
{
have : sin(x)**2 + cos(x)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
have : -sin(x)**4 + sin(x)**2 = (1 - sin(x)**2)*sin(x)**2,
{
ring_exp,
},
rw this,
rw sin_sq,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_400_MTEG_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : tan(x)≠ 0) (h3 : cos(-x+135*pi)≠ 0) (h4 : -cos(-x+135*pi)≠ 0) (h5 : sin(x)≠ 0) (h6 : cos(x+155*pi/2)≠ 0) (h7 : cos(x/2)≠ 0) (h8 : (2*tan(x/2))≠ 0) (h9 : (2*tan(x/2)/(1-tan(x/2)**2))≠ 0) (h10 : (1-tan(x/2)**2)≠ 0) : (1 + 2*tan(x/2)/(1 - tan(x/2)**2))*cos(x + 155*pi/2) + (-(1 - tan(x/2)**2)/(2*tan(x/2)) - 1)*cos(-x + 135*pi) - 1/cos(x + 155*pi/2) + 1/cos(-x + 135*pi)=0:=
begin
have : (-1 - 1 / (2 * tan(x / 2) / (1 - tan(x / 2) ** 2))) * cos(-x + 135 * pi) + (2 * tan(x / 2) / (1 - tan(x / 2) ** 2) + 1) * cos(x + 155 * pi / 2) - 1 / cos(x + 155 * pi / 2) + 1 / cos(-x + 135 * pi) = (1 + 2*tan(x/2)/(1 - tan(x/2)**2))*cos(x + 155*pi/2) + (-(1 - tan(x/2)**2)/(2*tan(x/2)) - 1)*cos(-x + 135*pi) - 1/cos(x + 155*pi/2) + 1/cos(-x + 135*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(x) = 2 * tan(x/2) / ( 1 - tan(x/2) ** 2 ),
{
have : tan(x) = tan(2*(x/2)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : -(1 + 1 / tan(x)) * cos(-x + 135 * pi) + (tan(x) + 1) * cos(x + 155 * pi / 2) + 1 / cos(-x + 135 * pi) - 1 / cos(x + 155 * pi / 2) = (-1 - 1/tan(x))*cos(-x + 135*pi) + (tan(x) + 1)*cos(x + 155*pi/2) - 1/cos(x + 155*pi/2) + 1/cos(-x + 135*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = cos(x + 155*pi/2),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (38),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 + 1 / tan(x)) * -cos(-x + 135 * pi) + (tan(x) + 1) * sin(x) - 1 / -cos(-x + 135 * pi) - 1 / sin(x) = -(1 + 1/tan(x))*cos(-x + 135*pi) + (tan(x) + 1)*sin(x) + 1/cos(-x + 135*pi) - 1/sin(x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = -cos(-x + 135*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (x) (67),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw one_div_div,
have : (1 + cos(x)/sin(x))*cos(x) + (sin(x)/cos(x) + 1)*sin(x) - 1/cos(x) - 1/sin(x) = (sin(x)**3 + sin(x)**2*cos(x) + sin(x)*cos(x)**2 + cos(x)**3 - sin(x) - cos(x))/(sin(x)*cos(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sin(x)**3 + sin(x)**2*cos(x) + sin(x)*cos(x)**2 + cos(x)**3 = (sin(x) + cos(x))*(sin(x)**2 + cos(x)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
end


lemma Trigo_6_401_GXBA_extend : (-3*cos(28337*pi/540) + 4*cos(28337*pi/540)**3)*cos(17*pi/180) + (-3*cos(28337*pi/540) + 4*cos(28337*pi/540)**3)**2 + cos(17*pi/90)/2 + 1/2=3/4:=
begin
have : cos(17 * pi / 180) * (4 * cos(28337 * pi / 540) ** 3 - 3 * cos(28337 * pi / 540)) + (4 * cos(28337 * pi / 540) ** 3 - 3 * cos(28337 * pi / 540)) ** 2 + cos(17 * pi / 90) / 2 + 1 / 2 = (-3*cos(28337*pi/540) + 4*cos(28337*pi/540)**3)*cos(17*pi/180) + (-3*cos(28337*pi/540) + 4*cos(28337*pi/540)**3)**2 + cos(17*pi/90)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(28337*pi/180) = 4 * cos(28337*pi/540) ** 3 - 3 * cos(28337*pi/540),
{
have : cos(28337*pi/180) = cos(3*(28337*pi/540)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : cos(17 * pi / 180) * cos(28337 * pi / 180) + cos(28337 * pi / 180) ** 2 + (cos(17 * pi / 90) / 2 + 1 / 2) = cos(17*pi/180)*cos(28337*pi/180) + cos(28337*pi/180)**2 + cos(17*pi/90)/2 + 1/2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/180) ** 2 = cos(17*pi/90) / 2 + 1 / 2,
{
have : cos(17*pi/90) = cos(2*(17*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(28337 * pi / 180)) ** 2 - -cos(28337 * pi / 180) * cos(17 * pi / 180) + cos(17 * pi / 180) ** 2 = cos(17*pi/180)*cos(28337*pi/180) + cos(28337*pi/180)**2 + cos(17*pi/180)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(13*pi/180) = -cos(28337*pi/180),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (13*pi/180) (78),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(17*pi/180) = sin(73*pi/180),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (17*pi/180) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(13*pi/180)**2 - sin(13*pi/180)*sin(73*pi/180) + sin(73*pi/180)**2 = sin(13*pi/180)*sin(73*pi/180) + (-sin(73*pi/180) + sin(13*pi/180))**2,
{
ring_exp,
},
rw this,
have : -sin(73*pi/180) + sin(13*pi/180) = 2*sin(-pi/6)*cos(43*pi/180),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((13*pi/180) + (73*pi/180))/2) = cos(43*pi/180),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((13*pi/180) - (73*pi/180))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
have : sin(-pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
have : sin(13*pi/180)*sin(73*pi/180) = -cos(43*pi/90)/2 + cos(-pi/3)/2,
{
rw sin_mul_sin,
have : cos((13*pi/180) + (73*pi/180)) = cos(43*pi/90),
{
apply congr_arg,
ring,
},
rw this,
have : cos((13*pi/180) - (73*pi/180)) = cos(-pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(-pi/3) = cos(pi/3),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
have : cos(43*pi/90) = -sin(43*pi/180)**2 + cos(43*pi/180)**2,
{
have : cos(43*pi/90) = cos(2*(43*pi/180)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
rw this,
ring_nf,
rw ← add_assoc,
have : 1/2*sin(43*pi/180)**2 + 1/2*cos(43*pi/180)**2 = 1/2,
{
have : sin(43*pi/180)**2 + cos(43*pi/180)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
norm_num,
end


lemma Trigo_6_402_DMDU_extend(h0 : 1 - tan(pi/18) * tan(5*pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : cos(5*pi/18) ≠ 0)  (h3 : cos(5*pi/36)≠ 0) (h4 : (1-tan(5*pi/36)**2)≠ 0) (h5 : ((1-1/tan(2723*pi/36)**2)*tan(2723*pi/36))≠ 0) (h6 : tan(2723*pi/36)≠ 0) (h7 : (1-((-1)/tan(2723*pi/36))**2)≠ 0) (h8 : cos((2723*pi/18)/2)≠ 0) (h9 : ((1-1/((1-cos(2723*pi/18))/sin(2723*pi/18))**2)*((1-cos(2723*pi/18))/sin(2723*pi/18)))≠ 0) (h10 : ((1-cos(2723*pi/18))*(-sin(2723*pi/18)**2/(1-cos(2723*pi/18))**2+1))≠ 0) (h11 : (1-cos(2723*pi/18))≠ 0) (h12 : ((1-cos(2723*pi/18))/sin(2723*pi/18))≠ 0) (h13 : sin(2723*pi/18)≠ 0) : tan(pi/18) - 2*sqrt(3)*sin(2723*pi/18)*tan(pi/18)/((1 - cos(2723*pi/18))*(-sin(2723*pi/18)**2/(1 - cos(2723*pi/18))**2 + 1)) - 2*sin(2723*pi/18)/((1 - cos(2723*pi/18))*(-sin(2723*pi/18)**2/(1 - cos(2723*pi/18))**2 + 1))=sqrt(3):=
begin
have : tan(pi / 18) - 2 * sqrt 3 * tan(pi / 18) / ((1 - 1 / ((1 - cos(2723 * pi / 18)) / sin(2723 * pi / 18)) ** 2) * ((1 - cos(2723 * pi / 18)) / sin(2723 * pi / 18))) - 2 / ((1 - 1 / ((1 - cos(2723 * pi / 18)) / sin(2723 * pi / 18)) ** 2) * ((1 - cos(2723 * pi / 18)) / sin(2723 * pi / 18))) = tan(pi/18) - 2*sqrt(3)*sin(2723*pi/18)*tan(pi/18)/((1 - cos(2723*pi/18))*(-sin(2723*pi/18)**2/(1 - cos(2723*pi/18))**2 + 1)) - 2*sin(2723*pi/18)/((1 - cos(2723*pi/18))*(-sin(2723*pi/18)**2/(1 - cos(2723*pi/18))**2 + 1)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(2723*pi/36) = ( 1 - cos(2723*pi/18) ) / sin(2723*pi/18),
{
have : tan(2723*pi/36) = tan((2723*pi/18)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : tan(pi / 18) + 2 * sqrt 3 * tan(pi / 18) * ((-1) / tan(2723 * pi / 36)) / (1 - ((-1) / tan(2723 * pi / 36)) ** 2) + 2 * ((-1) / tan(2723 * pi / 36)) / (1 - ((-1) / tan(2723 * pi / 36)) ** 2) = tan(pi/18) - 2*sqrt(3)*tan(pi/18)/((1 - 1/tan(2723*pi/36)**2)*tan(2723*pi/36)) - 2/((1 - 1/tan(2723*pi/36)**2)*tan(2723*pi/36)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/36) = -1 / tan(2723*pi/36),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (5*pi/36) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * tan(pi / 18) * (2 * tan(5 * pi / 36) / (1 - tan(5 * pi / 36) ** 2)) + tan(pi / 18) + 2 * tan(5 * pi / 36) / (1 - tan(5 * pi / 36) ** 2) = tan(pi/18) + 2*sqrt(3)*tan(pi/18)*tan(5*pi/36)/(1 - tan(5*pi/36)**2) + 2*tan(5*pi/36)/(1 - tan(5*pi/36)**2),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(5*pi/18) = 2 * tan(5*pi/36) / ( 1 - tan(5*pi/36) ** 2 ),
{
have : tan(5*pi/18) = tan(2*(5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw tan_two_mul,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
rw add_assoc,
have : tan(pi/18) + tan(5*pi/18) = (-tan(pi/18)*tan(5*pi/18) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/18) + (5*pi/18)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : (-tan(pi/18)*tan(5*pi/18) + 1)*tan(pi/3) = -tan(pi/18)*tan(5*pi/18)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
rw tan_pi_div_three,
norm_num,
ring_exp,
end


lemma Trigo_6_403_YJZW_extend : -cos(1349*pi/18)**2 + sqrt(3)*sin(1349*pi/18)*cos(2239*pi/18) + cos(2239*pi/18)**2 + 1=1/4:=
begin
have : -cos(1349 * pi / 18) ** 2 + sqrt 3 * cos(2239 * pi / 18) * sin(1349 * pi / 18) + cos(2239 * pi / 18) ** 2 + 1 = -cos(1349*pi/18)**2 + sqrt(3)*sin(1349*pi/18)*cos(2239*pi/18) + cos(2239*pi/18)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = cos(2239*pi/18),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 1 - cos(1349 * pi / 18) ** 2 + sqrt 3 * sin(pi / 9) * sin(1349 * pi / 18) + sin(pi / 9) ** 2 = -cos(1349*pi/18)**2 + sqrt(3)*sin(pi/9)*sin(1349*pi/18) + sin(pi/9)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(1349*pi/18) ** 2 = 1 - cos(1349*pi/18) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 9) ** 2 + sqrt 3 * sin(pi / 9) * sin(1349 * pi / 18) + sin(1349 * pi / 18) ** 2 = sin(1349*pi/18)**2 + sqrt(3)*sin(pi/9)*sin(1349*pi/18) + sin(pi/9)**2,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(4*pi/9) = sin(1349*pi/18),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (37),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sin_sq,
have : 1-cos(pi/9)**2 + sqrt(3)*sin(pi/9)*cos(4*pi/9) + cos(4*pi/9)**2 = -cos(pi/9)**2 + cos(4*pi/9)**2 + 1 + sqrt(3)*sin(pi/9)*cos(4*pi/9),
{
ring,
},
rw this,
have : -cos(pi/9)**2 + cos(4*pi/9)**2 = (-cos(pi/9) + cos(4*pi/9))*(cos(4*pi/9) + cos(pi/9)),
{
ring_exp,
},
rw this,
have : -cos(pi/9) + cos(4*pi/9) = -2*sin(pi/6)*sin(5*pi/18),
{
rw neg_add_eq_sub,
rw cos_sub_cos,
have : sin(((4*pi/9) + (pi/9))/2) = sin(5*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((4*pi/9) - (pi/9))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(4*pi/9) + cos(pi/9) = 2*cos(pi/6)*cos(5*pi/18),
{
rw cos_add_cos,
have : cos(((4*pi/9) + (pi/9))/2) = cos(5*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((4*pi/9) - (pi/9))/2) = cos(pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw sin_pi_div_six,
have : (-2)*(1/2)*sin(5*pi/18)*(2*cos(pi/6)*cos(5*pi/18)) = (-2)*(1/2)*(sin(5*pi/18)*cos(5*pi/18))*(2*cos(pi/6)),
{
ring,
},
rw this,
have : sin(5*pi/18)*cos(5*pi/18) = sin(5*pi/9)/2,
{
have : sin(5*pi/9) = 2*sin(5*pi/18)*cos(5*pi/18),
{
have : sin(5*pi/9) = sin(2*(5*pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(5*pi/9) = cos(pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_assoc (sqrt(3)) (sin(pi/9)) (cos(4*pi/9)),
have : sin(pi/9)*cos(4*pi/9) = -sin(pi/3)/2 + sin(5*pi/9)/2,
{
rw mul_comm,
rw cos_mul_sin,
have : sin((4*pi/9) + (pi/9)) = sin(5*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((4*pi/9) - (pi/9)) = sin(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : sin(5*pi/9) = cos(pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
rw sin_pi_div_three,
norm_num,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_6_404_BEVX_extend(h0 : sin(x) ≠ 0)  (h1 : (8*sin(x))≠ 0) : -(cos(-6*x + 43*pi)/2 + cos(2*x + 43*pi)/2)*cos(x)=-sin(8*x + 121*pi)/(8*sin(x)):=
begin
have : -(cos((-6) * x + 43 * pi) / 2 + cos(2 * x + 43 * pi) / 2) * cos(x) = -(cos(-6*x + 43*pi)/2 + cos(2*x + 43*pi)/2)*cos(x),
{
field_simp at *,
},
have : cos(-2*x + 43*pi) * cos(4*x) = cos(-6*x + 43*pi) / 2 + cos(2*x + 43*pi) / 2,
{
rw cos_mul_cos,
have : cos((-2*x + 43*pi) + (4*x)) = cos(2*x + 43*pi),
{
apply congr_arg,
ring,
},
rw this,
have : cos((-2*x + 43*pi) - (4*x)) = cos(-6*x + 43*pi),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : -(cos(-2*x + 43*pi) * cos(4*x))*cos(x) = -cos(x)*cos(4*x)*cos(-2*x+43*pi),
{
ring,
},
conv {to_lhs, rw this,},
have : sin(8*x) = -sin(8*x + 121*pi),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (8*x) (60),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_rhs, rw ← this,},
have : cos(x) * -cos((-2) * x + 43 * pi) * cos(4 * x) = -cos(x)*cos(4*x)*cos(-2*x + 43*pi),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*x) = -cos(-2*x + 43*pi),
{
rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*x) (21),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8*x) = 2*sin(4*x)*cos(4*x),
{
have : sin(8*x) = sin(2*(4*x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(4*x) = 2*sin(2*x)*cos(2*x),
{
have : sin(4*x) = sin(2*(2*x)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(2*x) = 2*sin(x)*cos(x),
{
have : sin(2*x) = sin(2*(x)),
{
apply congr_arg,
ring,
},
rw sin_two_mul,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_6_405_KQQA_extend(h0 : sin(pi/36) ≠ 0) (h1 : sin(pi/12) ≠ 0) (h2 : 2 - sqrt(3) ≠ 0) (h3 : (-cos(pi/9)+cos(pi/36)*cos(pi/12))≠ 0) (h4 : (cos(pi/36)*cos(pi/12)-cos(pi/9))≠ 0) (h5 : (-(-sin((-7)*pi/18)*sin(pi/2)+cos((-7)*pi/18)*cos(pi/2))+cos(pi/36)*cos(pi/12))≠ 0) (h6 : (sin(-7*pi/18)*sin(pi/2)-cos(-7*pi/18)*cos(pi/2)+cos(pi/36)*cos(pi/12))≠ 0) (h7 : (sin((-7)*pi/18)*sin(pi/2)-cos((-7)*pi/18)*cos(pi/2)+cos(pi/36)*cos(pi/12))≠ 0) : (-sin(pi/9) - cos(-473*pi/9)/2 - cos(947*pi/18)/2)/(sin(-7*pi/18)*sin(pi/2) - cos(-7*pi/18)*cos(pi/2) + cos(pi/36)*cos(pi/12))=-2-sqrt(3):=
begin
have : (-sin(pi / 9) - (cos((-473) * pi / 9) / 2 + cos(947 * pi / 18) / 2)) / (sin((-7) * pi / 18) * sin(pi / 2) - cos((-7) * pi / 18) * cos(pi / 2) + cos(pi / 36) * cos(pi / 12)) = (-sin(pi/9) - cos(-473*pi/9)/2 - cos(947*pi/18)/2)/(sin(-7*pi/18)*sin(pi/2) - cos(-7*pi/18)*cos(pi/2) + cos(pi/36)*cos(pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/36) * cos(631*pi/12) = cos(-473*pi/9) / 2 + cos(947*pi/18) / 2,
{
rw cos_mul_cos,
have : cos((pi/36) + (631*pi/12)) = cos(947*pi/18),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/36) - (631*pi/12)) = cos(-473*pi/9),
{
apply congr_arg,
ring,
},
rw this,
},
conv {to_lhs, rw ← this,},
have : (cos(pi/36) * cos(631*pi/12)) = cos(pi/36)*cos(631*pi/12),
{
ring,
},
have : (-sin(pi / 9) - cos(pi / 36) * cos(631 * pi / 12)) / (-(-sin((-7) * pi / 18) * sin(pi / 2) + cos((-7) * pi / 18) * cos(pi / 2)) + cos(pi / 36) * cos(pi / 12)) = (-sin(pi/9) - cos(pi/36)*cos(631*pi/12))/(sin(-7*pi/18)*sin(pi/2) - cos(-7*pi/18)*cos(pi/2) + cos(pi/36)*cos(pi/12)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -sin(-7*pi/18) * sin(pi/2) + cos(-7*pi/18) * cos(pi/2),
{
have : cos(pi/9) = cos((-7*pi/18) + (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-cos(631 * pi / 12) * cos(pi / 36) - sin(pi / 9)) / (cos(pi / 36) * cos(pi / 12) - cos(pi / 9)) = (-sin(pi/9) - cos(pi/36)*cos(631*pi/12))/(-cos(pi/9) + cos(pi/36)*cos(pi/12)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/12) = -cos(631*pi/12),
{
rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (pi/12) (26),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(pi/36)*cos(pi/12) + sin(pi/12)*cos(pi/36),
{
have : sin(pi/9) = sin((pi/12) + (pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
have : cos(pi/9) = -sin(pi/36)*sin(pi/12) + cos(pi/36)*cos(pi/12),
{
have : cos(pi/9) = cos((pi/12) + (pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
rw this,
ring_exp,
have : sin(pi/36)*(cos(pi/12)*-(sin(pi/12)*sin(pi/36))⁻¹) = -cos(pi/12)/sin(pi/12),
{
field_simp,
ring,
},
rw this,
rw neg_div,
rw ← one_div_div,
rw ← tan_eq_sin_div_cos,
rw tan_pi_div_twelve,
field_simp,
ring_exp,
rw sq_sqrt,
ring,
repeat {linarith},
end


lemma Trigo_6_406_OYPE_extend(h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0)  (h2 : (-sin(x)**6-cos(-x+22*pi)**6+1)≠ 0) (h3 : (-sin(x+110*pi)**6-cos(-x+22*pi)**6+1)≠ 0) (h4 : (-sin(x+110*pi)**6-cos(-x+137*pi)**6+1)≠ 0) (h5 : (-sin(x+110*pi)**6-(-cos(-x+137*pi))**6+1)≠ 0) : (-sin(x + 110*pi)**4 - cos(-x + 137*pi)**4 + 1)/(-sin(x + 110*pi)**6 - cos(-x + 137*pi)**6 + 1)=2/3:=
begin
have : (-sin(x + 110 * pi) ** 4 - (-cos(-x + 137 * pi)) ** 4 + 1) / (-sin(x + 110 * pi) ** 6 - (-cos(-x + 137 * pi)) ** 6 + 1) = (-sin(x + 110*pi)**4 - cos(-x + 137*pi)**4 + 1)/(-sin(x + 110*pi)**6 - cos(-x + 137*pi)**6 + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 22*pi) = -cos(-x + 137*pi),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-x + 22*pi) (57),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = sin(x + 110*pi),
{
rw sin_eq_sin_add_int_mul_two_pi (x) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = cos(-x + 22*pi),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (x) (11),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(x)**4 - cos(x)**4 = -(sin(x)**2 + cos(x)**2)**2 + 2*sin(x)**2*cos(x)**2,
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
have : -sin(x)**6 - cos(x)**6 = -(sin(x)**2 + cos(x)**2)**3 + 3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4,
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
have : -1 + 3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4 = -1 + (3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4),
{
ring,
},
rw this,
have : 3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4 = 3*sin(x)**2*cos(x)**2*(sin(x)**2 + cos(x)**2),
{
ring_exp,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_407_RYZJ_extend(h0 : sin(x) ≠ 0) (h1 : sin(x) - cos(x) + 1 ≠ 0) (h2 : sin(x)**2 - sin(x)*cos(x) + sin(x) ≠ 0) (h3 : cos(x) ≠ 0)  (h4 : ((1-cos(-x+183*pi/2))*tan(x)+cos(-x+183*pi/2))≠ 0) (h5 : ((-cos(-x+183*pi/2)+1)*tan(x)- -cos(-x+183*pi/2))≠ 0) (h6 : ((1-(1-2*sin(-x/2+183*pi/4)**2))*tan(x)+(1-2*sin(-x/2+183*pi/4)**2))≠ 0) (h7 : (2*sin(-x/2+183*pi/4)**2*tan(x)-2*sin(-x/2+183*pi/4)**2+1)≠ 0) (h8 : (2*sin(-x/2+815*pi/4)**2*tan(x)-2*sin(-x/2+815*pi/4)**2+1)≠ 0) : (2*sin(-x/2 + 815*pi/4)**2*tan(x) + 2*sin(-x/2 + 815*pi/4)**2 - 1)/(2*sin(-x/2 + 815*pi/4)**2*tan(x) - 2*sin(-x/2 + 815*pi/4)**2 + 1)=(tan(x)+sin(x))/(tan(x)*sin(x)):=
begin
have : sin(-x/2 + 183*pi/4) = sin(-x/2 + 815*pi/4),
{
rw sin_eq_sin_add_int_mul_two_pi (-x/2 + 183*pi/4) (79),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : ((1 - (1 - 2 * sin(-x / 2 + 183 * pi / 4) ** 2)) * tan(x) - (1 - 2 * sin(-x / 2 + 183 * pi / 4) ** 2)) / ((1 - (1 - 2 * sin(-x / 2 + 183 * pi / 4) ** 2)) * tan(x) + (1 - 2 * sin(-x / 2 + 183 * pi / 4) ** 2)) = (2*sin(-x/2 + 183*pi/4)**2*tan(x) + 2*sin(-x/2 + 183*pi/4)**2 - 1)/(2*sin(-x/2 + 183*pi/4)**2*tan(x) - 2*sin(-x/2 + 183*pi/4)**2 + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-x + 183*pi/2) = 1 - 2 * sin(-x/2 + 183*pi/4) ** 2,
{
have : cos(-x + 183*pi/2) = cos(2*(-x/2 + 183*pi/4)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : ((-cos(-x + 183 * pi / 2) + 1) * tan(x) + -cos(-x + 183 * pi / 2)) / ((-cos(-x + 183 * pi / 2) + 1) * tan(x) - -cos(-x + 183 * pi / 2)) = ((1 - cos(-x + 183*pi/2))*tan(x) - cos(-x + 183*pi/2))/((1 - cos(-x + 183*pi/2))*tan(x) + cos(-x + 183*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -cos(-x + 183*pi/2),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sin(x)/cos(x) + sin(x) = -1/cos(x)*(-sin(x)*cos(x) - sin(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : -sin(x)*cos(x) - sin(x) = (-cos(x) - 1)*sin(x),
{
ring_exp,
},
rw this,
have : (sin(x) + 1) * (sin(x) / cos(x)) = (sin(x)**2 + sin(x))/cos(x),
{
ring_exp,
},
rw this,
have : (sin(x)**2 + sin(x))/cos(x) + sin(x) = (sin(x)**2 + sin(x)*cos(x) + sin(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : (sin(x)**2 + sin(x))/cos(x) - sin(x) = (sin(x)**2 - sin(x)*cos(x) + sin(x))/cos(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : sin(x)**2 + sin(x)*cos(x) + sin(x) = (sin(x) + cos(x) + 1)*sin(x),
{
ring_exp,
},
rw this,
have : sin(x)**2 - sin(x)*cos(x) + sin(x) = (sin(x) - cos(x) + 1)*sin(x),
{
ring_exp,
},
rw this,
field_simp,
ring_exp,
have : cos(x) * sin(x) ** 2 = cos(x)*sin(x)**2*(sin(x)**2 + cos(x)**2),
{
rw sin_sq_add_cos_sq,
ring,
},
rw this,
ring,
end


lemma Trigo_6_408_NQVH_extend(h0 : sin(pi/9) ≠ 0)  (h1 : sin(pi/9)≠ 0) (h2 : cos((7*pi/9)/2)≠ 0) (h3 : sin(7*pi/9)≠ 0) : -8*cos(2*pi/27)**3 + sqrt(3)*(1 - cos(7*pi/9))*(sin(2*pi)*cos(-35*pi/18) + sin(-35*pi/18)*cos(2*pi))/sin(7*pi/9) + cos(pi/18)*cos(pi/9)/sin(pi/9) + 6*cos(2*pi/27)=2:=
begin
have : (-8) * cos(2 * pi / 27) ** 3 + sqrt 3 * (1 - cos(7 * pi / 9)) * (sin((-35) * pi / 18) * cos(2 * pi) + sin(2 * pi) * cos((-35) * pi / 18)) / sin(7 * pi / 9) + cos(pi / 18) * cos(pi / 9) / sin(pi / 9) + 6 * cos(2 * pi / 27) = -8*cos(2*pi/27)**3 + sqrt(3)*(1 - cos(7*pi/9))*(sin(2*pi)*cos(-35*pi/18) + sin(-35*pi/18)*cos(2*pi))/sin(7*pi/9) + cos(pi/18)*cos(pi/9)/sin(pi/9) + 6*cos(2*pi/27),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/18) = sin(-35*pi/18) * cos(2*pi) + sin(2*pi) * cos(-35*pi/18),
{
have : sin(pi/18) = sin((-35*pi/18) + (2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : (-8) * cos(2 * pi / 27) ** 3 + sqrt 3 * sin(pi / 18) * ((1 - cos(7 * pi / 9)) / sin(7 * pi / 9)) + cos(pi / 18) * cos(pi / 9) / sin(pi / 9) + 6 * cos(2 * pi / 27) = -8*cos(2*pi/27)**3 + sqrt(3)*(1 - cos(7*pi/9))*sin(pi/18)/sin(7*pi/9) + cos(pi/18)*cos(pi/9)/sin(pi/9) + 6*cos(2*pi/27),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/18) = ( 1 - cos(7*pi/9) ) / sin(7*pi/9),
{
have : tan(7*pi/18) = tan((7*pi/9)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : sqrt 3 * sin(pi / 18) * tan(7 * pi / 18) - 2 * (4 * cos(2 * pi / 27) ** 3 - 3 * cos(2 * pi / 27)) + cos(pi / 18) * cos(pi / 9) / sin(pi / 9) = -8*cos(2*pi/27)**3 + sqrt(3)*sin(pi/18)*tan(7*pi/18) + cos(pi/18)*cos(pi/9)/sin(pi/9) + 6*cos(2*pi/27),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = 4 * cos(2*pi/27) ** 3 - 3 * cos(2*pi/27),
{
have : cos(2*pi/9) = cos(3*(2*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/18) = 1/tan(pi/9),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
rw one_div_div,
rw sub_add_eq_add_sub,
have : sqrt(3)*sin(pi/18)*(cos(pi/9)/sin(pi/9)) + cos(pi/18)*cos(pi/9)/sin(pi/9) = (sqrt(3)*sin(pi/18) + cos(pi/18))*cos(pi/9)/sin(pi/9),
{
ring_exp,
},
rw this,
have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
{
field_simp,
},
rw this,
have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18) = 2*sin(2*pi/9),
{
have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
{
have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
linarith,
},
rw this,
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
ring_exp,
have : cos(pi/9)**2 = cos(2*pi/9)/2 + 1/2,
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
field_simp,
ring_exp,
end


lemma Trigo_6_409_DDFZ_extend(h0 : cos(pi/9) ≠ 0) (h1 : sin(pi/9) ≠ 0) (h2 : cos((2*pi/9)/2)≠ 0) (h3 : (1+cos(2*pi/9))≠ 0) (h4 : (cos(2*pi/9)+1)≠ 0) (h5 : tan(233*pi/9)≠ 0) : (-sqrt(3)*sin(2*pi/9)/(cos(2*pi/9) + 1) + 1)*cos(pi/18)/tan(233*pi/9)=-1:=
begin
have : -(-1 + sqrt 3 * sin(2 * pi / 9) / (cos(2 * pi / 9) + 1)) * cos(pi / 18) / tan(233 * pi / 9) = (-sqrt(3)*sin(2*pi/9)/(cos(2*pi/9) + 1) + 1)*cos(pi/18)/tan(233*pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : (-1 + sqrt 3 * sin(2 * pi / 9) / (cos(2 * pi / 9) + 1)) * cos(pi / 18) * ((-1) / tan(233 * pi / 9)) = -(-1 + sqrt(3)*sin(2*pi/9)/(cos(2*pi/9) + 1))*cos(pi/18)/tan(233*pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/18) = -1 / tan(233*pi/9),
{
rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7*pi/18) (25),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * (sin(2 * pi / 9) / (1 + cos(2 * pi / 9))) - 1) * cos(pi / 18) * tan(7 * pi / 18) = (-1 + sqrt(3)*sin(2*pi/9)/(cos(2*pi/9) + 1))*cos(pi/18)*tan(7*pi/18),
{
field_simp at *,
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
have : tan(7*pi/18) = 1/tan(pi/9),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw tan_eq_sin_div_cos,
have : sqrt(3)*(sin(pi/9)/cos(pi/9)) - 1 = (-cos(pi/9) + sqrt(3)*sin(pi/9))/cos(pi/9),
{
ring_exp,
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : sqrt(3)*sin(pi/9) = 2*sin(pi/9)*cos(pi/6),
{
field_simp,
ring_exp,
},
rw this,
have : cos(pi/9) = 2*sin(pi/6)*cos(pi/9),
{
field_simp,
},
rw this,
rw ← neg_mul,
rw ← neg_mul,
have : -2*sin(pi/6)*cos(pi/9) + 2*sin(pi/9)*cos(pi/6) = 2*sin(-pi/18),
{
have : sin(-pi/18) = sin(pi/9)*cos(pi/6) - sin(pi/6)*cos(pi/9),
{
have : sin(-pi/18) = sin((pi/9) - (pi/6)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : sin(-pi/18) = -sin(pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw div_mul_eq_mul_div,
rw mul_neg,
rw ← neg_mul,
have : -2*sin(pi/18)*cos(pi/18) = -sin(pi/9),
{
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_6_410_RSSE_extend(h0 : cos(pi/15) ≠ 0) (h1 : sin(4*pi/15) ≠ 0)  (h2 : ((4*sin(5893*pi/30)**2-2)*sin(pi/15))≠ 0) (h3 : ((-2+4*sin(5893*pi/30)**2)*sin(pi/15))≠ 0) (h4 : cos(5893*pi/30)≠ 0) (h5 : ((-2+sin(5893*pi/15)**2/cos(5893*pi/30)**2)*sin(pi/15))≠ 0) (h6 : ((-2+4*(sin(5893*pi/15)/(2*cos(5893*pi/30)))**2)*sin(pi/15))≠ 0) (h7 : cos(5893*pi/30)≠ 0) (h8 : (2*cos(5893*pi/30))≠ 0) : (-3 + sqrt(3)*tan(331*pi/15))/((-2 + sin(5893*pi/15)**2/cos(5893*pi/30)**2)*sin(pi/15))=-4*sqrt(3):=
begin
have : (-3 + sqrt 3 * tan(331 * pi / 15)) / ((-2 + 4 * (sin(5893 * pi / 15) / (2 * cos(5893 * pi / 30))) ** 2) * sin(pi / 15)) = (-3 + sqrt(3)*tan(331*pi/15))/((-2 + sin(5893*pi/15)**2/cos(5893*pi/30)**2)*sin(pi/15)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(5893*pi/30) = sin(5893*pi/15) / ( 2 * cos(5893*pi/30) ),
{
have : sin(5893*pi/15) = sin(2*(5893*pi/30)),
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
have : (-3 + sqrt 3 * tan(331 * pi / 15)) / ((-2 + 4 * sin(5893 * pi / 30) ** 2) * sin(pi / 15)) = (-3 + sqrt(3)*tan(331*pi/15))/((-2 + 4*sin(5893*pi/30)**2)*sin(pi/15)),
{
field_simp at *,
},
have : tan(pi/15) = tan(331*pi/15),
{
rw tan_eq_tan_add_int_mul_pi (pi/15) (22),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * tan(pi / 15) - 3) / ((4 * sin(5893 * pi / 30) ** 2 - 2) * sin(pi / 15)) = (-3 + sqrt(3)*tan(pi/15))/((-2 + 4*sin(5893*pi/30)**2)*sin(pi/15)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/15) = sin(5893*pi/30),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/15) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw sub_eq_add_neg (4*cos(pi/15)**2) 2,
have : -2 = -2*cos(pi/15)**2 - 2*sin(pi/15)**2,
{
have : sin(pi/15)**2 + cos(pi/15)**2 = 1,
{
rw sin_sq_add_cos_sq,
},
linarith,
},
rw this,
have : 4*cos(pi/15)**2 + ((-2)*cos(pi/15)**2 - 2*sin(pi/15)**2) = -2*sin(pi/15)**2 + 2*cos(pi/15)**2 ,
{
ring,
},
rw this,
have : -2*sin(pi/15)**2 + 2*cos(pi/15)**2 = 2*cos(2*pi/15),
{
have : cos(2*pi/15) = -sin(pi/15)**2 + cos(pi/15)**2,
{
have : cos(2*pi/15) = cos(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
linarith,
},
rw this,
have : sqrt(3)*(sin(pi/15)/cos(pi/15)) - 3 = (-3*cos(pi/15) + sqrt(3)*sin(pi/15))/cos(pi/15),
{
field_simp,
ring_exp,
},
rw this,
have : ((-3)*cos(pi/15) + sqrt(3)*sin(pi/15))/cos(pi/15)/(2*cos(2*pi/15)*sin(pi/15)) = ((-3)*cos(pi/15) + sqrt(3)*sin(pi/15))/(2*sin(pi/15)*cos(pi/15)*cos(2*pi/15)),
{
field_simp,
ring_exp,
},
rw this,
have : 2*sin(pi/15)*cos(pi/15) = sin(2*pi/15),
{
have : sin(2*pi/15) = sin(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
{
have : sin(4*pi/15) = 2*sin(2*pi/15)*cos(2*pi/15),
{
have : sin(4*pi/15) = sin(2*(2*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(pi/15) = 2*sin(pi/6)*cos(pi/15),
{
field_simp,
},
rw this,
have : sqrt(3)*sin(pi/15) = 2*cos(pi/6)*sin(pi/15),
{
field_simp,
ring_exp,
},
rw this,
have : (-3)*(2*sin(pi/6)*cos(pi/15)) + 2*cos(pi/6)*sin(pi/15) = -2*sin(pi/6)*cos(pi/15) + 2*cos(pi/6)*sin(pi/15) - 4*sin(pi/6)*cos(pi/15),
{
ring,
},
rw this,
rw mul_right_comm 2 (cos(pi/6)) (sin(pi/15)),
have : -2*sin(pi/6)*cos(pi/15) + 2*sin(pi/15)*cos(pi/6) = -2*sin(pi/10),
{
have : sin(pi/10) = -sin(pi/15)*cos(pi/6) + sin(pi/6)*cos(pi/15),
{
have : sin(pi/10) = sin((pi/6) - (pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
linarith,
},
rw this,
have : sin(pi/10) = cos(2*pi/5),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/10) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
have : (-2)*cos(2*pi/5) - 4*(1/2)*cos(pi/15) = -2*cos(pi/15) - 2*cos(2*pi/5),
{
ring,
},
rw this,
have : -2*cos(pi/15) - 2*cos(2*pi/5) = -4*cos(-pi/6)*cos(7*pi/30),
{
have : cos(pi/15) + cos(2*pi/5) = 2*cos(-pi/6)*cos(7*pi/30),
{
rw cos_add_cos,
have : cos(((pi/15) + (2*pi/5))/2) = cos(7*pi/30),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((pi/15) - (2*pi/5))/2) = cos(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
have : cos(-pi/6) = cos(pi/6),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
have : cos(7*pi/30) = sin(4*pi/15),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/30) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_411_BEZS_extend(h0 : cos(2*pi/15) ≠ 0) (h1 : tan((11*pi/90)+(23*pi/180)) ≠ 0) (h2 : 1 - tan(2*pi/15) * tan(7*pi/60) ≠ 0) (h3 : cos(7*pi/60) ≠ 0) (h4 : cos(23*pi/180) ≠ 0) (h5 : 1-tan(11*pi/90)*tan(23*pi/180) ≠ 0) (h6 : cos(11*pi/90) ≠ 0)  (h7 : cos((11*pi/45)/2)≠ 0) (h8 : sin(11*pi/45)≠ 0) (h9 : sin(8179*pi/45)≠ 0) (h10 : -sin(8179*pi/45)≠ 0) (h11 : (sin(8164*pi/45)*cos(pi/3)+sin(pi/3)*cos(8164*pi/45))≠ 0) : ((-1 + cos(11*pi/45))/(sin(8164*pi/45)*cos(pi/3) + sin(pi/3)*cos(8164*pi/45)) + 1)*(tan(7*pi/60) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1)=4:=
begin
have : (-(1 - cos(11 * pi / 45)) / (sin(8164 * pi / 45) * cos(pi / 3) + sin(pi / 3) * cos(8164 * pi / 45)) + 1) * (tan(7 * pi / 60) + 1) * (tan(23 * pi / 180) + 1) * (tan(2 * pi / 15) + 1) = ((-1 + cos(11*pi/45))/(sin(8164*pi/45)*cos(pi/3) + sin(pi/3)*cos(8164*pi/45)) + 1)*(tan(7*pi/60) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(8179*pi/45) = sin(8164*pi/45) * cos(pi/3) + sin(pi/3) * cos(8164*pi/45),
{
have : sin(8179*pi/45) = sin((8164*pi/45) + (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
conv {to_lhs, rw ← this,},
have : ((1 - cos(11 * pi / 45)) / -sin(8179 * pi / 45) + 1) * (tan(7 * pi / 60) + 1) * (tan(23 * pi / 180) + 1) * (tan(2 * pi / 15) + 1) = (-(1 - cos(11*pi/45))/sin(8179*pi/45) + 1)*(tan(7*pi/60) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(11*pi/45) = -sin(8179*pi/45),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (11*pi/45) (91),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(7 * pi / 60) + 1) * ((1 - cos(11 * pi / 45)) / sin(11 * pi / 45) + 1) * (tan(23 * pi / 180) + 1) * (tan(2 * pi / 15) + 1) = ((1 - cos(11*pi/45))/sin(11*pi/45) + 1)*(tan(7*pi/60) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(11*pi/90) = ( 1 - cos(11*pi/45) ) / sin(11*pi/45),
{
have : tan(11*pi/90) = tan((11*pi/45)/2),
{
apply congr_arg,
ring,
},
rw this,
rw tan_div_two,
repeat {assumption},
},
conv {to_lhs, rw ← this,},
have : (tan(7*pi/60) + 1)*(tan(11*pi/90) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1) = (tan(7*pi/60) + 1)*(tan(2*pi/15) + 1)*(tan(11*pi/90) + 1)*(tan(23*pi/180) + 1),
{
ring,
},
rw this,
have : (tan(7*pi/60) + 1)*(tan(2*pi/15) + 1) = tan(7*pi/60)*tan(2*pi/15) + tan(7*pi/60) + tan(2*pi/15) + 1,
{
ring_exp,
},
rw this,
rw add_assoc (tan(7*pi/60)*tan(2*pi/15)) (tan(7*pi/60)) (tan(2*pi/15)),
have : tan(7*pi/60) + tan(2*pi/15) = (-tan(7*pi/60)*tan(2*pi/15) + 1)*tan(pi/4),
{
rw add_comm,
rw tan_add_tan,
have : tan((2*pi/15) + (7*pi/60)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
rw mul_assoc,
have : (tan(11*pi/90) + 1)*(tan(23*pi/180) + 1) = tan(11*pi/90)*tan(23*pi/180) + tan(11*pi/90) + tan(23*pi/180) + 1,
{
ring_exp,
},
rw this,
have : tan(11*pi/90)*tan(23*pi/180) = -(tan(11*pi/90) + tan(23*pi/180))/tan(pi/4) + 1,
{
rw tan_mul_tan',
have : tan((11*pi/90) + (23*pi/180)) = tan(pi/4),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
rw this,
rw tan_pi_div_four,
norm_num,
ring_exp,
end


lemma Trigo_6_412_HKDG_extend(h0 : -sin(pi/36) + cos(pi/36) ≥ 0) (h1 : sin(4*pi/9) ≠ 0)  (h2 : (sqrt(1-sin(pi/18))*cos(2*pi/9))≠ 0) (h3 : (sqrt(1-sin(pi/18))*(-3*cos(2*pi/27)+4*cos(2*pi/27)**3))≠ 0) (h4 : (sqrt(1-sin(pi/18))*(4*cos(2*pi/27)**3-3*cos(2*pi/27)))≠ 0) (h5 : (sqrt(1-sin(pi/18))*((-3)*cos(2*pi/27)+4*cos(2*pi/27)**3))≠ 0) : (-sin(pi/36)**2 + (-sin(pi/72)**2 + cos(pi/72)**2)**2)/(sqrt(1 - sin(pi/18))*(-3*cos(2*pi/27) + 4*cos(2*pi/27)**3))=sqrt(2):=
begin
have : (-sin(pi / 36) ** 2 + (-sin(pi / 72) ** 2 + cos(pi / 72) ** 2) ** 2) / (sqrt (1 - sin(pi / 18)) * ((-3) * cos(2 * pi / 27) + 4 * cos(2 * pi / 27) ** 3)) = (-sin(pi/36)**2 + (-sin(pi/72)**2 + cos(pi/72)**2)**2)/(sqrt(1 - sin(pi/18))*(-3*cos(2*pi/27) + 4*cos(2*pi/27)**3)),
{
field_simp at *,
},
have : cos(pi/36) = -sin(pi/72) ** 2 + cos(pi/72) ** 2,
{
have : cos(pi/36) = cos(2*(pi/72)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul',
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(pi / 36) ** 2 + cos(pi / 36) ** 2) / (sqrt (1 - sin(pi / 18)) * (4 * cos(2 * pi / 27) ** 3 - 3 * cos(2 * pi / 27))) = (-sin(pi/36)**2 + cos(pi/36)**2)/(sqrt(1 - sin(pi/18))*(-3*cos(2*pi/27) + 4*cos(2*pi/27)**3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(2*pi/9) = 4 * cos(2*pi/27) ** 3 - 3 * cos(2*pi/27),
{
have : cos(2*pi/9) = cos(3*(2*pi/27)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_three_mul,
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
have : sin(pi/18) = 2*sin(pi/36)*cos(pi/36),
{
have : sin(pi/18) = sin(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : 1 - 2*sin(pi/36)*cos(pi/36) = sin(pi/36)**2 + cos(pi/36)**2 - 2*sin(pi/36)*cos(pi/36),
{
rw sin_sq_add_cos_sq,
},
rw this,
have : sin(pi/36)**2 + cos(pi/36)**2 -2*sin(pi/36)*cos(pi/36) = (-sin(pi/36) + cos(pi/36))**2,
{
ring_exp,
},
rw this,
rw sqrt_sq_eq_abs,
rw abs_eq_self.mpr h0,
have : sin(pi/36) = cos(17*pi/36),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : -cos(17*pi/36) + cos(pi/36) = 2*sin(2*pi/9)*sin(pi/4),
{
have : -cos(pi/36) + cos(17*pi/36) = -2*sin(2*pi/9)*sin(pi/4),
{
rw neg_add_eq_sub,
rw cos_sub_cos,
have : sin(((17*pi/36) + (pi/36))/2) = sin(pi/4),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((17*pi/36) - (pi/36))/2) = sin(2*pi/9),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
rw mul_right_comm (2*sin(2*pi/9)) (sin(pi/4)) (cos(2*pi/9)),
have : 2*sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9),
{
have : sin(4*pi/9) = sin(2*(2*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : cos(pi/18) = sin(4*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_four,
field_simp,
ring_nf,
rw sq_sqrt,
repeat {linarith},
end


lemma Trigo_6_413_QUEC_extend(h0 : cos(pi/36) ≠ 0) (h1 : cos(pi/36)≠ 0) (h2 : cos(397*pi/36)≠ 0) (h3 : -cos(397*pi/36)≠ 0) : -(sqrt(3)*cos(2357*pi/36) + 2*sin(3629*pi/36))/cos(397*pi/36)=1:=
begin
have : (sqrt 3 * cos(2357 * pi / 36) + 2 * sin(3629 * pi / 36)) / -cos(397 * pi / 36) = -(sqrt(3)*cos(2357*pi/36) + 2*sin(3629*pi/36))/cos(397*pi/36),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/36) = -cos(397*pi/36),
{
rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (pi/36) (5),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * cos(2357 * pi / 36) + 2 * sin(3629 * pi / 36)) / cos(pi / 36) = (sqrt(3)*cos(2357*pi/36) + 2*sin(3629*pi/36))/cos(pi/36),
{
field_simp at *,
},
have : cos(11*pi/36) = sin(3629*pi/36),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (50),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sqrt 3 * -cos(2357 * pi / 36) + 2 * cos(11 * pi / 36)) / cos(pi / 36) = (sqrt(3)*cos(2357*pi/36) + 2*cos(11*pi/36))/cos(pi/36),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(pi/36) = -cos(2357*pi/36),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/36) (32),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sqrt(3) = 2*sin(pi/3),
{
field_simp,
ring_exp,
},
rw this,
rw ← neg_mul,
rw mul_assoc,
have : sin(pi/3)*sin(pi/36) = -cos(13*pi/36)/2 + cos(11*pi/36)/2,
{
rw sin_mul_sin,
have : cos((pi/3) + (pi/36)) = cos(13*pi/36),
{
apply congr_arg,
ring,
},
rw this,
have : cos((pi/3) - (pi/36)) = cos(11*pi/36),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : (-2)*(-cos(13*pi/36)/2 + cos(11*pi/36)/2) + 2*cos(11*pi/36) = cos(13*pi/36) + cos(11*pi/36),
{
ring,
},
rw this,
have : cos(13*pi/36) + cos(11*pi/36) = 2*cos(-pi/36)*cos(pi/3),
{
rw add_comm,
rw cos_add_cos,
have : cos(((11*pi/36) + (13*pi/36))/2) = cos(pi/3),
{
apply congr_arg,
ring,
},
rw this,
have : cos(((11*pi/36) - (13*pi/36))/2) = cos(-pi/36),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
have : cos(-pi/36) = cos(pi/36),
{
rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
field_simp,
end


lemma Trigo_6_414_SIUE_extend(h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/15) ≠ 0) (h2 : sin(pi/15) ≠ 0) (h3 : cos(2*pi/15) ≠ 0) (h4 : sin(4*pi/15) ≠ 0)  (h5 : ((2*cos(931*pi/15)**2-1)*sin(pi/15))≠ 0) (h6 : ((-1+2*cos(931*pi/15)**2)*sin(pi/15))≠ 0) (h7 : ((-1+2*cos(931*pi/15)**2)*sin(1441*pi/15))≠ 0) (h8 : ((-1+2*sin(6167*pi/30)**2)*sin(1441*pi/15))≠ 0) (h9 : ((-1+2*(-sin(6167*pi/30))**2)*sin(1441*pi/15))≠ 0) : (-sqrt(3) + tan(pi/15))/((-1 + 2*sin(6167*pi/30)**2)*sin(1441*pi/15))=-8:=
begin
have : (-sqrt 3 + tan(pi / 15)) / ((-1 + 2 * (-sin(6167 * pi / 30)) ** 2) * sin(1441 * pi / 15)) = (-sqrt(3) + tan(pi/15))/((-1 + 2*sin(6167*pi/30)**2)*sin(1441*pi/15)),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(931*pi/15) = -sin(6167*pi/30),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (931*pi/15) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sqrt 3 + tan(pi / 15)) / ((-1 + 2 * cos(931 * pi / 15) ** 2) * sin(1441 * pi / 15)) = (-sqrt(3) + tan(pi/15))/((-1 + 2*cos(931*pi/15)**2)*sin(1441*pi/15)),
{
field_simp at *,
},
have : sin(pi/15) = sin(1441*pi/15),
{
rw sin_eq_sin_add_int_mul_two_pi (pi/15) (48),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 15) - sqrt 3) / ((2 * cos(931 * pi / 15) ** 2 - 1) * sin(pi / 15)) = (-sqrt(3) + tan(pi/15))/((-1 + 2*cos(931*pi/15)**2)*sin(pi/15)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/15) = cos(931*pi/15),
{
rw cos_eq_cos_add_int_mul_two_pi (pi/15) (31),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2*cos(pi/15)**2 -1 = cos(2*pi/15),
{
have : cos(2*pi/15) = cos(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
rw this,
have : sqrt(3) = tan(pi/3),
{
rw tan_pi_div_three,
},
rw this,
have : tan(pi/15) - tan(pi/3) = sin(-4*pi/15)/(cos(pi/15)*cos(pi/3)),
{
rw tan_sub_tan',
have : sin((pi/15) - (pi/3)) = sin(-4*pi/15),
{
apply congr_arg,
ring,
},
rw this,
repeat {assumption},
},
rw this,
have : sin((-4)*pi/15)/(cos(pi/15)*cos(pi/3))/(cos(2*pi/15)*sin(pi/15)) = sin((-4)*pi/15)/(sin(pi/15)*cos(pi/15)*cos(pi/3)*cos(2*pi/15)),
{
field_simp,
left,
ring,
},
rw this,
have : sin(pi/15)*cos(pi/15) = sin(2*pi/15)/2,
{
have : sin(2*pi/15) = 2*sin(pi/15)*cos(pi/15),
{
have : sin(2*pi/15) = sin(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*pi/15)/2*cos(pi/3)*cos(2*pi/15) = sin(2*pi/15)*cos(2*pi/15)/2*cos(pi/3),
{
ring,
},
rw this,
have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
{
have : sin(4*pi/15) = 2*sin(2*pi/15)*cos(2*pi/15),
{
have : sin(4*pi/15) = sin(2*(2*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(-4*pi/15) = -sin(4*pi/15),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-4*pi/15) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_6_415_NIFN_extend(h0 : cos(pi/9) ≠ 0) (h1 : cos(pi/9)≠ 0) : (-sin(pi/9) - 2*sin(-pi)*sin(19*pi/18) + (-2 + 4*(sin(-5*pi/2)*sin(-2*pi) + cos(-5*pi/2)*cos(-2*pi))**2)*cos(19*pi/18))/cos(pi/9)=sqrt(3):=
begin
have : (-sin(pi / 9) - 2 * sin(-pi) * sin(19 * pi / 18) + 2 * (-1 + 2 * (sin((-5) * pi / 2) * sin((-2) * pi) + cos((-5) * pi / 2) * cos((-2) * pi)) ** 2) * cos(19 * pi / 18)) / cos(pi / 9) = (-sin(pi/9) - 2*sin(-pi)*sin(19*pi/18) + (-2 + 4*(sin(-5*pi/2)*sin(-2*pi) + cos(-5*pi/2)*cos(-2*pi))**2)*cos(19*pi/18))/cos(pi/9),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
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
have : (-sin(pi / 9) - 2 * sin(-pi) * sin(19 * pi / 18) + 2 * (2 * cos(-pi / 2) ** 2 - 1) * cos(19 * pi / 18)) / cos(pi / 9) = (-sin(pi/9) - 2*sin(-pi)*sin(19*pi/18) + 2*(-1 + 2*cos(-pi/2)**2)*cos(19*pi/18))/cos(pi/9),
{
field_simp at *,
repeat {left},
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
have : (-sin(pi / 9) + 2 * (-sin(19 * pi / 18) * sin(-pi) + cos(19 * pi / 18) * cos(-pi))) / cos(pi / 9) = (-sin(pi/9) - 2*sin(-pi)*sin(19*pi/18) + 2*cos(-pi)*cos(19*pi/18))/cos(pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = -sin(19*pi/18) * sin(-pi) + cos(19*pi/18) * cos(-pi),
{
have : cos(pi/18) = cos((19*pi/18) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = sin(4*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(4*pi/9) = sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
{
have : sin(4*pi/9) = sin((pi/3) + (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_add,
ring,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_6_416_ZILP_extend(h0 : cos(pi/10) ≠ 0) (h1 : sin(2*pi/5) ≠ 0) (h2 : sin(pi/15)≠ 0) (h3 : (2*sin(pi/15))≠ 0) (h4 : (2*cos(4513*pi/30))≠ 0) : -sin(2*pi/15)/(2*cos(4513*pi/30)) - sin(pi)*cos(13*pi/10) + sin(7*pi/30) + sin(13*pi/10)*cos(pi)=1/2:=
begin
have : -sin(2 * pi / 15) / (2 * cos(4513 * pi / 30)) + sin(7 * pi / 30) + (sin(13 * pi / 10) * cos(pi) - sin(pi) * cos(13 * pi / 10)) = -sin(2*pi/15)/(2*cos(4513*pi/30)) - sin(pi)*cos(13*pi/10) + sin(7*pi/30) + sin(13*pi/10)*cos(pi),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(3*pi/10) = sin(13*pi/10) * cos(pi) - sin(pi) * cos(13*pi/10),
{
have : sin(3*pi/10) = sin((13*pi/10) - (pi)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/15) = cos(4513*pi/30),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/15) (75),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7 * pi / 30) + sin(3 * pi / 10) - sin(2 * pi / 15) / (2 * sin(pi / 15)) = -sin(2*pi/15)/(2*sin(pi/15)) + sin(7*pi/30) + sin(3*pi/10),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/15) = sin(2*pi/15) / ( 2 * sin(pi/15) ),
{
have : sin(2*pi/15) = sin(2*(pi/15)),
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
have : sin(7*pi/30) = cos(4*pi/15),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/30) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw ← sub_add_eq_add_sub,
have : cos(4*pi/15) - cos(pi/15) = -2*sin(pi/10)*sin(pi/6),
{
rw cos_sub_cos,
have : sin(((4*pi/15) + (pi/15))/2) = sin(pi/6),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((4*pi/15) - (pi/15))/2) = sin(pi/10),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
rw this,
rw sin_pi_div_six,
have : sin(3*pi/10) = -4*sin(pi/10)**3 + 3*sin(pi/10),
{
have : sin(3*pi/10) = sin(3*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
rw this,
have : (-2)*sin(pi/10)*(1/2) + ((-4)*sin(pi/10)**3 + 3*sin(pi/10)) = 2*sin(pi/10)*(1 - 2*sin(pi/10)**2),
{
ring_exp,
},
rw this,
have : 1 - 2*sin(pi/10)**2 = cos(pi/5),
{
have : cos(pi/5) = cos(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
rw this,
have : sin(pi/10) = sin(pi/5)/(2*cos(pi/10)),
{
have : sin(pi/5) = sin(2*(pi/10)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
field_simp,
ring,
},
rw this,
have : 2*(sin(pi/5)/(2*cos(pi/10)))*cos(pi/5) = 2*(sin(pi/5)*cos(pi/5))/(2*cos(pi/10)),
{
ring,
},
rw this,
have : sin(pi/5)*cos(pi/5) = sin(2*pi/5)/2,
{
have : sin(2*pi/5) = 2*sin(pi/5)*cos(pi/5),
{
have : sin(2*pi/5) = sin(2*(pi/5)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(pi/10) = sin(2*pi/5),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/10) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_6_417_SNCF_extend(h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/15) ≠ 0) (h2 : sin(pi/15) ≠ 0) (h3 : cos(2*pi/15) ≠ 0) (h4 : sin(4*pi/15) ≠ 0)  (h5 : ((4*cos(pi/15)**2-2)*((-4)*sin(pi/45)**3+3*sin(pi/45)))≠ 0) (h6 : ((-2+4*cos(pi/15)**2)*(-4*sin(pi/45)**3+3*sin(pi/45)))≠ 0) (h7 : ((-2+4*cos(pi/15)**2)*(4*cos(10033*pi/90)**3-3*cos(10033*pi/90)))≠ 0) (h8 : ((-2+4*cos(pi/15)**2)*((-4)*(-cos(10033*pi/90))**3+3*-cos(10033*pi/90)))≠ 0) (h9 : cos(pi/15)≠ 0) : (-3 + sqrt(3)*sin(pi/15)/cos(pi/15))/((-2 + 4*cos(pi/15)**2)*(4*cos(10033*pi/90)**3 - 3*cos(10033*pi/90)))=-4*sqrt(3):=
begin
have : (-3 + sqrt 3 * (sin(pi / 15) / cos(pi / 15))) / ((-2 + 4 * cos(pi / 15) ** 2) * (4 * cos(10033 * pi / 90) ** 3 - 3 * cos(10033 * pi / 90))) = (-3 + sqrt(3)*sin(pi/15)/cos(pi/15))/((-2 + 4*cos(pi/15)**2)*(4*cos(10033*pi/90)**3 - 3*cos(10033*pi/90))),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : tan(pi/15) = sin(pi/15) / cos(pi/15),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (-3 + sqrt 3 * tan(pi / 15)) / ((-2 + 4 * cos(pi / 15) ** 2) * ((-4) * (-cos(10033 * pi / 90)) ** 3 + 3 * -cos(10033 * pi / 90))) = (-3 + sqrt(3)*tan(pi/15))/((-2 + 4*cos(pi/15)**2)*(4*cos(10033*pi/90)**3 - 3*cos(10033*pi/90))),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/45) = -cos(10033*pi/90),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (pi/45) (55),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sqrt 3 * tan(pi / 15) - 3) / ((4 * cos(pi / 15) ** 2 - 2) * ((-4) * sin(pi / 45) ** 3 + 3 * sin(pi / 45))) = (-3 + sqrt(3)*tan(pi/15))/((-2 + 4*cos(pi/15)**2)*(-4*sin(pi/45)**3 + 3*sin(pi/45))),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/15) = -4 * sin(pi/45) ** 3 + 3 * sin(pi/45),
{
have : sin(pi/15) = sin(3*(pi/45)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_three_mul,
ring,
},
conv {to_lhs, rw ← this,},
have : 4*cos(pi/15)**2 -2 = 2*cos(2*pi/15),
{
have : cos(2*pi/15) = 2*cos(pi/15)**2 - 1,
{
have : cos(2*pi/15) = cos(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
},
linarith,
},
rw this,
have : sqrt(3)*tan(pi/15) -3 = -sqrt(3)*(-tan(pi/15) + sqrt(3)),
{
ring_exp,
rw sq_sqrt,
ring_exp,
linarith,
},
rw this,
have : sqrt(3) = tan(pi/3),
{
field_simp,
},
rw this,
have : -tan(pi/15) + tan(pi/3) = sin(4*pi/15)/(cos(pi/15)*cos(pi/3)),
{
rw neg_add_eq_sub,
rw tan_sub_tan',
have : sin((pi/3) - (pi/15)) = sin(4*pi/15),
{
apply congr_arg,
ring,
},
rw this,
field_simp,
repeat {assumption},
},
rw this,
have : -tan(pi/3)*(sin(4*pi/15)/(cos(pi/15)*cos(pi/3)))/(2*cos(2*pi/15)*sin(pi/15)) = -tan(pi/3)*sin(4*pi/15)/(2*sin(pi/15)*cos(pi/15)*cos(2*pi/15)*cos(pi/3)),
{
field_simp,
ring,
},
rw this,
have : 2*sin(pi/15)*cos(pi/15) = sin(2*pi/15),
{
have : sin(2*pi/15) = sin(2*(pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
{
have : sin(4*pi/15) = 2*sin(2*pi/15)*cos(2*pi/15),
{
have : sin(4*pi/15) = sin(2*(2*pi/15)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
rw tan_pi_div_three,
rw cos_pi_div_three,
field_simp,
ring_exp,
end


lemma Trigo_6_418_BATW_extend(h0 : cos(pi/9) ≠ 0)  (h1 : cos(pi/9)≠ 0) : -4*sin(pi/3)*cos(4*pi/9) + (-sin(pi/3)*cos(4*pi/9) + sin(4*pi/9)*sin(1037*pi/6))/cos(pi/9) + 4*sin(4*pi/9)*sin(1037*pi/6)=sqrt(3):=
begin
have : (-4) * sin(pi / 3) * cos(4 * pi / 9) + (-sin(pi / 3) * cos(4 * pi / 9) + sin(4 * pi / 9) * sin(1037 * pi / 6)) / cos(pi / 9) + 4 * sin(4 * pi / 9) * sin(1037 * pi / 6) = -4*sin(pi/3)*cos(4*pi/9) + (-sin(pi/3)*cos(4*pi/9) + sin(4*pi/9)*sin(1037*pi/6))/cos(pi/9) + 4*sin(4*pi/9)*sin(1037*pi/6),
{
field_simp at *,
},
have : cos(pi/3) = sin(1037*pi/6),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (pi/3) (86),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (sin(4 * pi / 9) * cos(pi / 3) - sin(pi / 3) * cos(4 * pi / 9)) / cos(pi / 9) + 4 * (sin(4 * pi / 9) * cos(pi / 3) - sin(pi / 3) * cos(4 * pi / 9)) = -4*sin(pi/3)*cos(4*pi/9) + (-sin(pi/3)*cos(4*pi/9) + sin(4*pi/9)*cos(pi/3))/cos(pi/9) + 4*sin(4*pi/9)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(4*pi/9) * cos(pi/3) - sin(pi/3) * cos(4*pi/9),
{
have : sin(pi/9) = sin((4*pi/9) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * sin(pi / 9) + sin(pi / 9) / cos(pi / 9) = sin(pi/9)/cos(pi/9) + 4*sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = sin(pi/9) / cos(pi/9),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : 4*sin(pi/9) + sin(pi/9)/cos(pi/9) = (sin(pi/9) + 4*sin(pi/9)*cos(pi/9))/cos(pi/9),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw mul_assoc,
have : sin(pi/9)*cos(pi/9) = sin(2*pi/9)/2,
{
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*pi/9) = -sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
{
have : sin(2*pi/9) = sin((pi/3) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_419_RVIC_extend(h0 : 4 ≠ 0) (h1 : cos(pi/9) ≠ 0)  : -sin(pi/3)*cos(4*pi/9) + tan(pi/9)/4 + sin(23*pi/9)*cos(pi/3)=sqrt(3)/4:=
begin
have : -sin(pi / 3) * cos(4 * pi / 9) + tan(pi / 9) / 4 + cos(pi / 3) * sin(23 * pi / 9) = -sin(pi/3)*cos(4*pi/9) + tan(pi/9)/4 + sin(23*pi/9)*cos(pi/3),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(1655*pi/18) = sin(23*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (1655*pi/18) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -sin(pi / 3) * cos(4 * pi / 9) + tan(pi / 9) / 4 + cos(1655 * pi / 18) * cos(pi / 3) = -sin(pi/3)*cos(4*pi/9) + tan(pi/9)/4 + cos(pi/3)*cos(1655*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(4*pi/9) = cos(1655*pi/18),
{
rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (4*pi/9) (45),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(4 * pi / 9) * cos(pi / 3) - sin(pi / 3) * cos(4 * pi / 9) + tan(pi / 9) / 4 = -sin(pi/3)*cos(4*pi/9) + tan(pi/9)/4 + sin(4*pi/9)*cos(pi/3),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(4*pi/9) * cos(pi/3) - sin(pi/3) * cos(4*pi/9),
{
have : sin(pi/9) = sin((4*pi/9) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : sin(pi/9) + sin(pi/9) / cos(pi/9)/4 = (sin(pi/9) + 4*sin(pi/9)*cos(pi/9))/(4*cos(pi/9)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw mul_assoc,
have : sin(pi/9)*cos(pi/9) = sin(2*pi/9)/2,
{
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*pi/9) = -sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
{
have : sin(2*pi/9) = sin((pi/3) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_420_EELP_extend(h0 : cos(4*pi/9) ≠ 0) (h1 : 3-cos(pi/9) ≠ 0)  (h2 : (2-cos(pi/18)**2)≠ 0) (h3 : (2-(1-2*sin(pi/36)**2)**2)≠ 0) (h4 : cos(3553*pi/18)≠ 0) (h5 : (2*cos(3553*pi/18))≠ 0) : (sin(3553*pi/9)/(2*cos(3553*pi/18)) + 3)*(-4 + 8*sin(pi/36)**2 + tan(4*pi/9))/(2 - (1 - 2*sin(pi/36)**2)**2)=2*sqrt(3):=
begin
have : sin(3553*pi/18) = sin(3553*pi/9) / ( 2 * cos(3553*pi/18) ),
{
have : sin(3553*pi/9) = sin(2*(3553*pi/18)),
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
have : (sin(3553 * pi / 18) + 3) * ((-4) * (1 - 2 * sin(pi / 36) ** 2) + tan(4 * pi / 9)) / (2 - (1 - 2 * sin(pi / 36) ** 2) ** 2) = (sin(3553*pi/18) + 3)*(-4 + 8*sin(pi/36)**2 + tan(4*pi/9))/(2 - (1 - 2*sin(pi/36)**2)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = 1 - 2 * sin(pi/36) ** 2,
{
have : cos(pi/18) = cos(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
},
conv {to_lhs, rw ← this,},
have : (3 - -sin(3553 * pi / 18)) * ((-4) * cos(pi / 18) + tan(4 * pi / 9)) / (2 - cos(pi / 18) ** 2) = (sin(3553*pi/18) + 3)*(-4*cos(pi/18) + tan(4*pi/9))/(2 - cos(pi/18)**2),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = -sin(3553*pi/18),
{
rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/18) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18)**2 = cos(pi/9)/2 + 1/2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
have : sin(7*pi/18) = cos(pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : 2 - (cos(pi/9)/2 + 1/2) = 3/2 - cos(pi/9)/2,
{
ring,
},
rw this,
have : (3 - cos(pi/9))*((-4)*cos(pi/18) + tan(4*pi/9))/(3/2 - cos(pi/9)/2) = (3 - cos(pi/9))/(3/2 - cos(pi/9)/2)*(-4*cos(pi/18) + tan(4*pi/9)),
{
field_simp,
ring,
},
rw this,
have : (3 - cos(pi/9))/(3/2 - cos(pi/9)/2) = 2,
{
have : 3/2 - cos(pi/9)/2 = (3 - cos(pi/9))/2,
{
ring,
},
rw this,
field_simp,
ring,
},
rw this,
rw tan_eq_sin_div_cos,
have : -4*cos(pi/18) + sin(4*pi/9)/cos(4*pi/9) = (-4*cos(pi/18)*cos(4*pi/9) + sin(4*pi/9))/cos(4*pi/9),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : cos(pi/18) = sin(4*pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw mul_assoc,
have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
{
have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
{
have : sin(8*pi/9) = sin(2*(4*pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(8*pi/9) = sin(pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/9) = -sin(pi/3)*cos(4*pi/9) + sin(4*pi/9)*cos(pi/3),
{
have : sin(pi/9) = sin((4*pi/9) - (pi/3)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_421_URXJ_extend(h0 : cos(pi/9) ≠ 0)  (h1 : cos(pi/9)≠ 0) (h2 : (-sin(10*pi/9)*sin(-pi)+cos(10*pi/9)*cos(-pi))≠ 0) (h3 : (-sin(-pi)*sin(10*pi/9)+cos(-pi)*cos(10*pi/9))≠ 0) (h4 : (-sin(-pi)*sin(10*pi/9)+cos(-pi)*cos(856*pi/9))≠ 0) : sin(pi/9)/(-sin(-pi)*sin(10*pi/9) + cos(-pi)*cos(856*pi/9)) + 4*sin(pi/9)=sqrt(3):=
begin
have : cos(10*pi/9) = cos(856*pi/9),
{
rw cos_eq_cos_add_int_mul_two_pi (10*pi/9) (47),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi / 9) / (-sin(10 * pi / 9) * sin(-pi) + cos(10 * pi / 9) * cos(-pi)) + 4 * sin(pi / 9) = sin(pi/9)/(-sin(-pi)*sin(10*pi/9) + cos(-pi)*cos(10*pi/9)) + 4*sin(pi/9),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/9) = -sin(10*pi/9) * sin(-pi) + cos(10*pi/9) * cos(-pi),
{
have : cos(pi/9) = cos((10*pi/9) + (-pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : 4 * sin(pi / 9) + sin(pi / 9) / cos(pi / 9) = sin(pi/9)/cos(pi/9) + 4*sin(pi/9),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/9) = sin(pi/9) / cos(pi/9),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
have : 4*sin(pi/9) + sin(pi/9)/cos(pi/9) = (sin(pi/9) + 4*sin(pi/9)*cos(pi/9))/cos(pi/9),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
rw mul_assoc,
have : sin(pi/9)*cos(pi/9) = sin(2*pi/9)/2,
{
have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
{
have : sin(2*pi/9) = sin(2*(pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : sin(2*pi/9) = -sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
{
have : sin(2*pi/9) = sin((pi/3) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
rw this,
rw cos_pi_div_three,
rw sin_pi_div_three,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_422_EEVG_extend (h0 : cos(-5*pi/36)≠ 0) (h1 : (2*cos(-5*pi/36))≠ 0) (h2 : (2*cos((-5)*pi/36))≠ 0) : -cos(-5*pi/36)**2 + sin(329*pi/18)*cos(11*pi/36)/(2*cos(-5*pi/36)) + cos(11*pi/36)**2 + 1=3/4:=
begin
have : -cos((-5) * pi / 36) ** 2 - -sin(329 * pi / 18) * cos(11 * pi / 36) / (2 * cos((-5) * pi / 36)) + cos(11 * pi / 36) ** 2 + 1 = -cos(-5*pi/36)**2 + sin(329*pi/18)*cos(11*pi/36)/(2*cos(-5*pi/36)) + cos(11*pi/36)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/18) = -sin(329*pi/18),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (9),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -cos((-5) * pi / 36) ** 2 - sin((-5) * pi / 18) / (2 * cos((-5) * pi / 36)) * cos(11 * pi / 36) + cos(11 * pi / 36) ** 2 + 1 = -cos(-5*pi/36)**2 - sin(-5*pi/18)*cos(11*pi/36)/(2*cos(-5*pi/36)) + cos(11*pi/36)**2 + 1,
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/36) = sin(-5*pi/18) / ( 2 * cos(-5*pi/36) ),
{
have : sin(-5*pi/18) = sin(2*(-5*pi/36)),
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
have : 1 - cos((-5) * pi / 36) ** 2 - sin((-5) * pi / 36) * cos(11 * pi / 36) + cos(11 * pi / 36) ** 2 = -cos(-5*pi/36)**2 - sin(-5*pi/36)*cos(11*pi/36) + cos(11*pi/36)**2 + 1,
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/36) ** 2 = 1 - cos(-5*pi/36) ** 2,
{
rw sin_sq,
},
conv {to_lhs, rw ← this,},
have : sin(-5*pi/36) = -sin(5*pi/36),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/36) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw neg_sq,
have : sin(5*pi/36)**2 = 1/2 - cos(5*pi/18)/2,
{
have : cos(5*pi/18) = cos(2*(5*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul'',
ring,
},
rw this,
have : cos(11*pi/36)**2 = cos(11*pi/18)/2 + 1/2,
{
have : cos(11*pi/18) = cos(2*(11*pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
rw this,
rw neg_mul,
have : sin(5*pi/36)*cos(11*pi/36) = sin(-pi/6)/2 + sin(4*pi/9)/2,
{
rw sin_mul_cos,
have : sin((5*pi/36) + (11*pi/36)) = sin(4*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin((5*pi/36) - (11*pi/36)) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
rw sub_neg_eq_add,
have : 1/2 - cos(5*pi/18)/2 + (sin(-pi/6)/2 + sin(4*pi/9)/2) + (cos(11*pi/18)/2 + 1/2) = 1 + (-cos(5*pi/18)/2 + cos(11*pi/18)/2) + (sin(-pi/6)/2 + sin(4*pi/9)/2),
{
ring,
},
rw this,
have : -cos(5*pi/18)/2 + cos(11*pi/18)/2 = sin(-pi/6)*sin(4*pi/9),
{
have : cos(5*pi/18) - cos(11*pi/18) = -2*sin(-pi/6)*sin(4*pi/9),
{
rw cos_sub_cos,
have : sin(((5*pi/18) + (11*pi/18))/2) = sin(4*pi/9),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((5*pi/18) - (11*pi/18))/2) = sin(-pi/6),
{
apply congr_arg,
ring,
},
rw this,
ring,
},
linarith,
},
rw this,
have : sin(-pi/6) = -sin(pi/6),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw sin_pi_div_six,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_423_MYOI_extend(h0 : 1 - tan(pi/10) * tan(7*pi/30) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : cos(7*pi/30) ≠ 0) (h3 : tan(pi/10) ≠ 0) (h4 : tan(7*pi/30) ≠ 0) (h5: sqrt 3 ≠ 0) (h6 : (tan(7*pi/30)*tan(pi/3))≠ 0) (h7 : (1/tan(412*pi/5)*tan(7*pi/30)*tan(pi/3))≠ 0) (h8 : tan(412*pi/5)≠ 0) (h9 : (tan(-99*pi/10)*tan(7*pi/30)*tan(pi/3))≠ 0) (h10 : tan((-99)*pi/10)≠ 0) (h11 : (1/tan((-99)*pi/10))≠ 0) (h12 : cos(7*pi/30)≠ 0) (h13 : (sin(7*pi/30)*tan(-99*pi/10)*tan(pi/3))≠ 0) (h14 : (tan((-99)*pi/10)*(sin(7*pi/30)/cos(7*pi/30))*tan(pi/3))≠ 0) : (tan(2*pi/3) + tan(-99*pi/10) + sin(7*pi/30)/cos(7*pi/30))*cos(7*pi/30)/(sin(7*pi/30)*tan(-99*pi/10)*tan(pi/3))=-1:=
begin
have : (tan(2 * pi / 3) + tan((-99) * pi / 10) + sin(7 * pi / 30) / cos(7 * pi / 30)) / (tan((-99) * pi / 10) * (sin(7 * pi / 30) / cos(7 * pi / 30)) * tan(pi / 3)) = (tan(2*pi/3) + tan(-99*pi/10) + sin(7*pi/30)/cos(7*pi/30))*cos(7*pi/30)/(sin(7*pi/30)*tan(-99*pi/10)*tan(pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(7*pi/30) = sin(7*pi/30) / cos(7*pi/30),
{
rw tan_eq_sin_div_cos,
},
conv {to_lhs, rw ← this,},
have : (tan(2 * pi / 3) + 1 / (1 / tan((-99) * pi / 10)) + tan(7 * pi / 30)) * (1 / tan((-99) * pi / 10)) / (tan(7 * pi / 30) * tan(pi / 3)) = (tan(2*pi/3) + tan(-99*pi/10) + tan(7*pi/30))/(tan(-99*pi/10)*tan(7*pi/30)*tan(pi/3)),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : tan(412*pi/5) = 1 / tan(-99*pi/10),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (412*pi/5) (72),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (1 / tan(412 * pi / 5) + tan(7 * pi / 30) + tan(2 * pi / 3)) / (1 / tan(412 * pi / 5) * tan(7 * pi / 30) * tan(pi / 3)) = (tan(2*pi/3) + 1/tan(412*pi/5) + tan(7*pi/30))*tan(412*pi/5)/(tan(7*pi/30)*tan(pi/3)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) = 1 / tan(412*pi/5),
{
rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (pi/10) (82),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : tan(pi/10) + tan(7*pi/30) = (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
{
rw tan_add_tan,
have : tan((pi/10) + (7*pi/30)) = tan(pi/3),
{
apply congr_arg,
ring,
},
rw this,
ring,
repeat {assumption},
},
rw this,
have : tan(2*pi/3) = -tan(pi/3),
{
rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3) = -tan(pi/10)*tan(7*pi/30)*tan(pi/3) + tan(pi/3),
{
ring_exp,
},
rw this,
field_simp,
end


lemma Trigo_6_424_JQLY_extend(h0 : sin(pi/36) ≠ 0) (h1 : cos(pi/36) ≠ 0) (h2 : sin(pi/18) ≠ 0) (h3 : cos(pi/18) ≠ 0)  (h4 : (sin(8*pi/9)*cos(pi/2)-sin(pi/2)*cos(8*pi/9)+1)≠ 0) (h5 : tan(pi/36)≠ 0) (h6 : (-sin(352*pi/9)*cos(pi/2)-sin(pi/2)*cos(8*pi/9)+1)≠ 0) (h7 : cos(352*pi/9)≠ 0) (h8 : (-sin(704*pi/9)*cos(pi/2)/(2*cos(352*pi/9))-sin(pi/2)*cos(8*pi/9)+1)≠ 0) (h9 : (2*cos(352*pi/9))≠ 0) (h10 : (-(sin(704*pi/9)/(2*cos(352*pi/9)))*cos(pi/2)-sin(pi/2)*cos(8*pi/9)+1)≠ 0) : (-1/tan(pi/36) + tan(pi/36))*cos(7*pi/18)/(-sin(704*pi/9)*cos(pi/2)/(2*cos(352*pi/9)) - sin(pi/2)*cos(8*pi/9) + 1)=-2:=
begin
have : ((-1) / tan(pi / 36) + tan(pi / 36)) * cos(7 * pi / 18) / (-(sin(704 * pi / 9) / (2 * cos(352 * pi / 9))) * cos(pi / 2) - sin(pi / 2) * cos(8 * pi / 9) + 1) = (-1/tan(pi/36) + tan(pi/36))*cos(7*pi/18)/(-sin(704*pi/9)*cos(pi/2)/(2*cos(352*pi/9)) - sin(pi/2)*cos(8*pi/9) + 1),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : sin(352*pi/9) = sin(704*pi/9) / ( 2 * cos(352*pi/9) ),
{
have : sin(704*pi/9) = sin(2*(352*pi/9)),
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
have : ((-1) / tan(pi / 36) + tan(pi / 36)) * cos(7 * pi / 18) / (-sin(352 * pi / 9) * cos(pi / 2) - sin(pi / 2) * cos(8 * pi / 9) + 1) = (-1/tan(pi/36) + tan(pi/36))*cos(7*pi/18)/(-sin(352*pi/9)*cos(pi/2) - sin(pi/2)*cos(8*pi/9) + 1),
{
field_simp at *,
},
have : sin(8*pi/9) = -sin(352*pi/9),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (8*pi/9) (20),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (tan(pi / 36) - 1 / tan(pi / 36)) * cos(7 * pi / 18) / (sin(8 * pi / 9) * cos(pi / 2) - sin(pi / 2) * cos(8 * pi / 9) + 1) = (-1/tan(pi/36) + tan(pi/36))*cos(7*pi/18)/(sin(8*pi/9)*cos(pi/2) - sin(pi/2)*cos(8*pi/9) + 1),
{
field_simp at *,
repeat {left},
ring,
},
conv {to_lhs, rw ← this,},
have : sin(7*pi/18) = sin(8*pi/9) * cos(pi/2) - sin(pi/2) * cos(8*pi/9),
{
have : sin(7*pi/18) = sin((8*pi/9) - (pi/2)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_sub,
ring,
},
conv {to_lhs, rw ← this,},
rw tan_eq_sin_div_cos,
rw one_div_div,
have : sin(pi/36)/cos(pi/36) - cos(pi/36)/sin(pi/36) = (-cos(pi/36)**2 + sin(pi/36)**2)/(sin(pi/36)*cos(pi/36)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three],
ring_exp,
},
rw this,
have : -cos(pi/36)**2 + sin(pi/36)**2 = -cos(pi/18),
{
have : cos(pi/18) = -sin(pi/36)**2 + cos(pi/36)**2,
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
linarith,
},
rw this,
have : sin(pi/36)*cos(pi/36) = sin(pi/18)/2,
{
have : sin(pi/18) = 2*sin(pi/36)*cos(pi/36),
{
have : sin(pi/18) = sin(2*(pi/36)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
linarith,
},
rw this,
have : cos(7*pi/18) = sin(pi/9),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
{
have : sin(pi/9) = sin(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw sin_two_mul,
},
rw this,
have : sin(7*pi/18) = cos(pi/9),
{
rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
have : cos(pi/9) + 1 = 2*cos(pi/18)**2,
{
have : cos(pi/18)**2 = cos(pi/9)/2 + 1/2,
{
have : cos(pi/9) = cos(2*(pi/18)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_two_mul,
ring,
},
linarith,
},
rw this,
field_simp,
ring_exp,
end


lemma Trigo_6_425_MXKD_extend(h0 : sin(x) ≠ 0) (h1 : 1 - cos(x) ≠ 0)  (h2 : (1-sin(x+385*pi/2))≠ 0) (h3 : sin(x)≠ 0) (h4 : -sin(-x+66*pi)≠ 0) (h5 : sin(-x+66*pi)≠ 0) (h6 : (1- -cos(-x-75*pi))≠ 0) (h7 : (cos(-x-75*pi)+1)≠ 0) : (1 - cos(-x - 75*pi))/sin(-x + 66*pi) - sin(-x + 66*pi)/(cos(-x - 75*pi) + 1)=0:=
begin
have : -(- -cos(-x - 75 * pi) - 1) / sin(-x + 66 * pi) - sin(-x + 66 * pi) / (1 - -cos(-x - 75 * pi)) = (1 - cos(-x - 75*pi))/sin(-x + 66*pi) - sin(-x + 66*pi)/(cos(-x - 75*pi) + 1),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x + 385*pi/2) = -cos(-x - 75*pi),
{
rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 385*pi/2) (58),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : -(sin(x + 385 * pi / 2) + 1) / -sin(-x + 66 * pi) + -sin(-x + 66 * pi) / (1 - sin(x + 385 * pi / 2)) = -(-sin(x + 385*pi/2) - 1)/sin(-x + 66*pi) - sin(-x + 66*pi)/(1 - sin(x + 385*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) = -sin(-x + 66*pi),
{
rw sin_eq_neg_sin_neg_add_int_mul_two_pi (x) (33),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x) / (1 - sin(x + 385 * pi / 2)) - (1 + sin(x + 385 * pi / 2)) / sin(x) = -(sin(x + 385*pi/2) + 1)/sin(x) + sin(x)/(1 - sin(x + 385*pi/2)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x) = sin(x + 385*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x) (96),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(x)/(1 - cos(x)) - (1 + cos(x))/sin(x) = (sin(x)**2 - (1 - cos(x))*(cos(x) + 1))/((1 - cos(x))*sin(x)),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
ring_exp,
},
rw this,
have : (1 - cos(x))*(cos(x) + 1) = 1 - cos(x)**2,
{
ring_exp,
},
rw this,
have : sin(x) ** 2 - (1 - cos(x) ** 2) = sin(x) ** 2 + cos(x) ** 2 - 1,
{
ring,
},
rw this,
rw sin_sq_add_cos_sq,
norm_num,
end


lemma Trigo_6_426_ANRK_extend(h0 : sin(x) ≠ 0)  (h1 : sin(x)≠ 0) (h2 : cos(2*x + y)≠ 0) (h3 : (2*cos(2*x+y))≠ 0) (h4 : (2*sin(x)*cos(2*x+y))≠ 0) (h5 : (2*sin(x)*sin(2*x+y+393*pi/2))≠ 0) : 2*sin(x + y + 283*pi/2) - sin(y)/sin(x) + sin(4*x + 2*y)/(2*sin(x)*sin(2*x + y + 393*pi/2))=0:=
begin
have : cos(2*x + y) = sin(2*x + y + 393*pi/2),
{
rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*x + y) (98),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : 2 * sin(x + y + 283 * pi / 2) - sin(y) / sin(x) + sin(4 * x + 2 * y) / (2 * cos(2 * x + y)) / sin(x) = 2*sin(x + y + 283*pi/2) - sin(y)/sin(x) + sin(4*x + 2*y)/(2*sin(x)*cos(2*x + y)),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(2*x + y) = sin(4*x + 2*y) / ( 2 * cos(2*x + y) ),
{
have : sin(4*x + 2*y) = sin(2*(2*x + y)),
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
have : (-2) * -sin(x + y + 283 * pi / 2) + sin(2 * x + y) / sin(x) - sin(y) / sin(x) = 2*sin(x + y + 283*pi/2) - sin(y)/sin(x) + sin(2*x + y)/sin(x),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(x + y) = -sin(x + y + 283*pi/2),
{
rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + y) (70),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
rw sub_eq_add_neg,
rw add_right_comm,
rw add_assoc,
rw ← neg_div,
have : -sin(y)/sin(x) + sin(2*x + y)/sin(x) = (-sin(y) + sin(2*x + y))/sin(x),
{
field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
},
rw this,
have : -sin(y) + sin(2*x + y) = 2*sin(x)*cos(x + y),
{
rw neg_add_eq_sub,
rw sin_sub_sin,
have : cos(((2*x + y) + (y))/2) = cos(x + y),
{
apply congr_arg,
ring,
},
rw this,
have : sin(((2*x + y) - (y))/2) = sin(x),
{
apply congr_arg,
ring,
},
rw this,
},
rw this,
norm_num,
field_simp,
ring_exp,
end


lemma Trigo_6_427_VHTP_extend(h0 : sin(7*pi/18) ≠ 0) (h1 : sin(7*pi/18)≠ 0) : (-sin(1124*pi/9) - 2*sin(-2*pi)*sin(37*pi/18) + 2*cos(37*pi/18)*cos(140*pi))/sin(7*pi/18)=sqrt(3):=
begin
have : (-sin(1124 * pi / 9) - 2 * sin((-2) * pi) * sin(37 * pi / 18) + 2 * cos(140 * pi) * cos(37 * pi / 18)) / sin(7 * pi / 18) = (-sin(1124*pi/9) - 2*sin(-2*pi)*sin(37*pi/18) + 2*cos(37*pi/18)*cos(140*pi))/sin(7*pi/18),
{
field_simp at *,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(-2*pi) = cos(140*pi),
{
rw cos_eq_cos_add_int_mul_two_pi (-2*pi) (71),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : (-sin(1124 * pi / 9) + 2 * (-sin(37 * pi / 18) * sin((-2) * pi) + cos(37 * pi / 18) * cos((-2) * pi))) / sin(7 * pi / 18) = (-sin(1124*pi/9) - 2*sin(-2*pi)*sin(37*pi/18) + 2*cos(-2*pi)*cos(37*pi/18))/sin(7*pi/18),
{
field_simp at *,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = -sin(37*pi/18) * sin(-2*pi) + cos(37*pi/18) * cos(-2*pi),
{
have : cos(pi/18) = cos((37*pi/18) + (-2*pi)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_add,
ring,
},
conv {to_lhs, rw ← this,},
have : sin(pi/9) = sin(1124*pi/9),
{
rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (62),
focus{repeat {apply congr_arg _}},
simp,
ring,
},
conv {to_lhs, rw ← this,},
have : cos(pi/18) = sin(pi/9)*sin(pi/6) + cos(pi/9)*cos(pi/6),
{
have : cos(pi/18) = cos((pi/6) - (pi/9)),
{
apply congr_arg,
ring,
},
rw this,
rw cos_sub,
ring,
},
rw this,
rw sin_pi_div_six,
have : cos(pi/9) = sin(7*pi/18),
{
rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (0),
repeat {apply congr_arg _},
simp,
linarith,
},
rw this,
rw cos_pi_div_six,
field_simp,
ring_exp,
end
