import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_5_350_KKXN (h0 : cos(23*pi/180) ≠ 0) (h1 : cos(11*pi/90) ≠ 0) (h2 : 1 - tan(11*pi/90) * tan(23*pi/180) ≠ 0) : tan(11*pi/90)*tan(23*pi/180) + tan(11*pi/90) + tan(23*pi/180)=1:=
begin
  rw add_assoc,
  have : tan(11*pi/90) + tan(23*pi/180)  =  (-tan(11*pi/90)*tan(23*pi/180) + 1)*tan(pi/4),
  {
  rw tan_add_tan,
  have : tan((11*pi/90) + (23*pi/180)) = tan (pi/4),
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

lemma Trigo_5_351_AIJZ (h0 : 2 ≠ 0) (h1 : 2*sin(x)*cos(x) + 2*cos(x) ≠ 0) (h2 : sin(x)/2 + 1/2 ≠ 0) (h3 : sin(x) + 1 ≠ 0) (h4 : 1 + sin(x) ≠ 0) : (-sin(2*x) + 2*cos(x))/(sin(2*x) + 2*cos(x))=tan(-x/2 + pi/4)**2:=
begin

  have : -sin(2*x)  =  -2*sin(x)*cos(x),
  {
  have : sin(2*x) = 2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  rw this,
  have : (-2*sin(x)*cos(x) + 2*cos(x))/(2*sin(x)*cos(x) + 2*cos(x))  =  (1 - sin(x))/(sin(x) + 1),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  rw div_pow,
  have : sin(-x/2 + pi/4)**2  =  1/2 - cos(-x+pi/2)/2,
  {
  have : cos (-x + pi/2) = cos(2*(-x/2 + pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(-x/2 + pi/4)**2  =  1/2 + cos(-x+pi/2)/2,
  {
  have : cos (-x + pi/2) = cos(2*(-x/2 + pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  have : cos(-x+pi/2)  =  sin(x),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_5_352_IIIT : -2*sin(x)*cos(x + y) + sin(2*x + y)=sin(y):=
begin
  have : cos(x + y)  =  -sin(x)*sin(y) + cos(x)*cos(y),
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
  have : sin(2*x + y)  =  sin(2*x)*cos(y) + sin(y)*cos(2*x),
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
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  rw this,
  have : cos(2*x)  =  1 - 2*sin(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_two_mul'',
  },
  rw this,
  have : sin(y)*(1 - 2*sin(x)**2)  =  -2*sin(x)**2*sin(y) + sin(y),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw mul_assoc,
  have : sin(x)*(-sin(x)*sin(y) + cos(x)*cos(y)) =  -sin(x)**2*sin(y) + sin(x)*cos(x)*cos(y),
  {
  ring_exp,
  },
  rw this,
  norm_num,
  ring_exp,
end

lemma Trigo_5_353_DGDW (h0 : cos(x/2) ≠ 0) (h1 : cos(x) ≠ 0) : (tan(x/2)*tan(x) + 1)*sin(2*x)/(2*cos(x))=tan(x):=
begin
  rw tan_eq_sin_div_cos,
  rw tan_eq_sin_div_cos,
  have : sin(x/2)/cos(x/2)*(sin(x)/cos(x)) + 1  =  (sin(x/2)*sin(x) + cos(x/2)*cos(x))/(cos(x/2)*cos(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : sin(x/2)*sin(x) + cos(x/2)*cos(x)  =  cos(x/2),
  {
  rw add_comm,
  rw ← cos_sub,
  rw ← cos_neg (x/2),
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_5_354_GNBL : sin(4*pi/3)*cos(25*pi/6)*tan(5*pi/4)=-3/4:=
begin
  have : sin(4*pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(25*pi/6)  =  cos(pi/6),
  {
  rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(5*pi/4)  =  tan(pi/4),
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

lemma Trigo_5_355_QVHL (h0 : cos(pi/18) ≠ 0) (h1 : sin(4*pi/9) ≠ 0) : 2*(sqrt(3)*tan(pi/18) + 1)*cos(2*pi/9)=2:=
begin
  rw tan_eq_sin_div_cos,
  have : sqrt(3)*(sin(pi/18)/cos(pi/18)) + 1  =  (sqrt(3)*sin(pi/18) + cos(pi/18))/cos(pi/18),
  {
  ring_exp,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sqrt(3)*sin(pi/18)  =  2*cos(pi/6)*sin(pi/18),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  rw mul_right_comm 2 (cos(π/6)) (sin(π/18)),
  have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18)  =  2*sin(2*pi/9),
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
  have : 2*(2*sin(2*π/9)/(2*sin(π/6)*cos(π/18)))*cos(2*π/9) = 2*2*(sin(2*π/9)*cos(2*π/9)/(2*sin(π/6)*cos(π/18))),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/9)*cos(2*pi/9)  =  sin(4*pi/9)/2,
  {
  have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
  {
  have : sin (4*pi/9) = sin(2*(2*pi/9)),
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
  have : cos(pi/18)  =  sin(4*pi/9),
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

lemma Trigo_5_356_KJSS (h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/10) ≠ 0) : (-tan(pi/10) + sqrt(3))/(sqrt(3)*tan(pi/10) + 1)=tan(7*pi/30):=
begin
  have : sqrt(3)  =  tan(pi/3),
  {
  field_simp,
  },
  rw this,
  rw mul_comm,
  have : (-tan(pi/10) + tan(pi/3))/(tan(pi/10)*tan(pi/3) + 1)  =  tan(7*pi/30),
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

lemma Trigo_5_357_SLFQ (h0 : sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : sin(pi/9) ≠ 0) : -sqrt(3)/cos(pi/18) + 1/sin(pi/18)=4:=
begin
  have : -sqrt(3)/cos(pi/18) + 1/sin(pi/18)  =  (-sqrt(3)*sin(pi/18) + cos(pi/18))/(sin(pi/18)*cos(pi/18)),
  {
  ring_exp,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  left,
  ring_exp,
  },
  rw this,
  have : -sqrt(3)*sin(pi/18)  =  -2*sin(pi/18)*sin(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*cos(pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : -2*sin(pi/18)*sin(pi/3) + 2*cos(pi/18)*cos(pi/3)  =  2*cos(7*pi/18),
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
  have : cos(7*pi/18)  =  sin(pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_assoc,
  have : cos(pi/18)*cos(pi/3)  =  cos(pi/18)/2,
  {
  field_simp,
  },
  rw this,
  have : sin(π/18)*(2*(cos(π/18)/2)) = sin(π/18)*cos(π/18),
  {
  ring,
  },
  rw this,
  have : sin(pi/18)*cos(pi/18) = sin(pi/9)/2,
  {
  have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
  {
  have : sin (pi/9) = sin(2*(pi/18)),
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

lemma Trigo_5_358_OIJT (h0 : sin(x) + cos(x) + 1 ≠ 0) : (sin(x) + sin(2*x) + cos(x) + 1)/(sin(x) + cos(x) + 1)-sqrt(2)*sin(x+pi/4)=0:=
begin
  have : sin(x + pi/4)  =  sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
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
  have : sqrt(2)*(sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x))  =  sin(x) + cos(x),
  {
  ring_exp,
  rw sq_sqrt,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  linarith,
  },
  rw this,
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
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
  have : 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2  =  (sin(x) + cos(x))**2,
  {
  ring_exp,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_5_359_PLXD (h0 : cos(y) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : 1 - tan(x) * tan(y) ≠ 0) (h3 : tan(x) ≠ 0) (h4: tan(x + y) ≠ 0) : (-tan(x) - tan(y) + tan(x + y))/(tan(x)*tan(x + y))=tan(y):=
begin
  have : -tan(x) - tan(y)  =  -tan(x + y)*(-tan(x)*tan(y) + 1),
  {
  have : tan(x) + tan(y) = (-tan(x)*tan(y) + 1)*tan(x + y),
  {
  rw tan_add_tan,
  have : tan((x) + (y)) = tan (x + y),
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
  have : -tan(x + y)*(-tan(x)*tan(y) + 1) + tan(x + y)  =  tan(x)*tan(y)*tan(x + y),
  {
  ring_exp,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_5_360_XQHO (h0 : sin(pi/9) ≠ 0) : sin(5*pi/18)*sin(17*pi/18)*cos(pi/9)=1/8:=
begin
  have : sin(5*pi/18)  =  cos(2*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(17*pi/18)  =  cos(4*pi/9),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (17*pi/18) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/9)  =  sin(2*pi/9)/(2*sin(pi/9)),
  {
  have : sin (2*pi/9) = sin(2*(pi/9)),
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
  have : cos(2*π/9)*cos(4*π/9)*(sin(2*π/9)/(2*sin(π/9))) = sin(2*π/9)*cos(2*π/9)*cos(4*π/9)/(2*sin(π/9)),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/9)*cos(2*pi/9)  =  sin(4*pi/9)/2,
  {
  have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
  {
  have : sin (4*pi/9) = sin(2*(2*pi/9)),
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
  have : sin(4*π/9)/2*cos(4*π/9) = sin(4*pi/9)*cos(4*pi/9)/2,
  {
  ring,
  },
  rw this,
  have : sin(4*pi/9)*cos(4*pi/9)  =  sin(8*pi/9)/2,
  {
  have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
  {
  have : sin (8*pi/9) = sin(2*(4*pi/9)),
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
  have : sin(8*pi/9)  =  sin(pi/9),
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

lemma Trigo_5_361_KOPV (h0 : sin(pi/18) ≥ 0) (h1 : -cos(pi/18) + sin(pi/18) ≤ 0) (h2 : -sin(pi/18) + cos(pi/18) ≠ 0) : sqrt(1 - sin(pi/9))/(-sqrt(1 - cos(17*pi/18)**2) + cos(35*pi/18))=1:=
begin
  rw ← sin_sq,
  have : sin(pi/9)  =  2*sin(pi/18)*cos(pi/18),
  {
  have : sin (pi/9) = sin(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 1 - 2*sin(π/18)*cos(π/18) = sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(pi/18)*cos(pi/18),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(pi/18)*cos(pi/18)  =  (-cos(pi/18) + sin(pi/18))**2,
  {
  ring_exp,
  },
  rw this,
  have : sin(17*pi/18)  =  sin(pi/18),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(35*pi/18)  =  cos(pi/18),
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

lemma Trigo_5_362_MKTN (h0 : 1 - tan(pi/10) * tan(7*pi/30) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : cos(7*pi/30) ≠ 0) (h3 : tan(pi/10) ≠ 0) (h4 : tan(7*pi/30) ≠ 0) (h5 : sqrt(3) ≠ 0) : (tan(pi/10) + tan(7*pi/30) + tan(2*pi/3))/(tan(pi/10)*tan(7*pi/30)*tan(pi/3))=-1:=
begin
  have : tan(2*pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(pi/10) + tan(7*pi/30)  =  (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((pi/10) + (7*pi/30)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3)  =  -tan(pi/10)*tan(7*pi/30)*tan(pi/3) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  field_simp,
end

lemma Trigo_5_363_KGWA (h0 : -cos(pi/18) + sin(pi/18) ≠ 0) (h1 : -sin(pi/18) + cos(pi/18) ≥ 0) (h2 : cos(pi/18) ≥ 0) : sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - sin(pi/18)**2) + sin(pi/18))=-1:=
begin
  have : -2*sin(π/18)*cos(π/18) + 1 = -2*sin(pi/18)*cos(pi/18) + (sin(pi/18)**2 + cos(pi/18)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : -2*sin(pi/18)*cos(pi/18) + (sin(pi/18)**2 + cos(pi/18)**2)  =  (-sin(pi/18) + cos(pi/18))**2,
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

lemma Trigo_5_364_FKRF (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x + 3*pi/2)*cos(-x + 2*pi)*tan(pi - x)/(sin(-x - pi)*cos(-x - pi))=-1:=
begin
  have : sin(-x + 3*pi/2)  =  -cos(x),
  {
  rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 3*pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + 2*pi)  =  cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(pi - x)  =  -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (pi - x) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(-x - pi)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x - pi)  =  -cos(x),
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

lemma Trigo_5_365_BJJC (h0 : sin(x) ≠ 0) (h1 : tan(x) ≠ 0) : -sin(pi - x)*cos(-x + 2*pi)*tan(pi - x)/(sin(-x - pi)*tan(-x - pi))=-cos(x):=
begin
  have : sin(pi - x)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 2*pi)  =  cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(pi - x)  =  -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (pi - x) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(-x - pi)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(-x - pi)  =  -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_5_366_SYGI (h0 : sin(pi/9) ≠ 0) : (sin(7*pi/36)**2 - 1/2)/(sin(pi/18)*cos(pi/18))=-1:=
begin
  have : sin(7*pi/36)**2  =  1/2 - cos(7*pi/18)/2,
  {
  have : cos (7*pi/18) = cos(2*(7*pi/36)),
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
  have : sin (pi/9) = sin(2*(pi/18)),
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
  have : cos(7*pi/18)  =  sin(pi/9),
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

lemma Trigo_5_367_SYMU (h0 : 2 ≠ 0) : -sin(x - pi/6)*cos(x + pi/6) + sin(x + pi/6)*cos(x - pi/6)=sqrt(3)/2:=
begin
  have : -sin(x - pi/6)  =  -sin(x)*cos(pi/6) + sin(pi/6)*cos(x),
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
  have : cos(x + pi/6)  =  -sin(pi/6)*sin(x) + cos(pi/6)*cos(x),
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
  have : sin(x + pi/6)  =  sin(x)*cos(pi/6) + sin(pi/6)*cos(x),
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
  have : cos(x - pi/6)  =  sin(pi/6)*sin(x) + cos(pi/6)*cos(x),
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
  have : (-sin(x)*(sqrt(3)/2) + 1/2*cos(x))*(-(1/2)*sin(x) + sqrt(3)/2*cos(x)) + (sin(x)*(sqrt(3)/2) + 1/2*cos(x))*(1/2*sin(x) + sqrt(3)/2*cos(x))  =  sqrt(3)*(sin(x)**2 + cos(x)**2)/2,
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
end

lemma Trigo_5_368_BLFE (h0 : -sin(x) + cos(x) ≠ 0) : cos(2*x)/sin(-x + pi/4)-2*sin(x+pi/4)=0:=
begin
  have : 2*sin(x + pi/4)  =  2*sin(x)*cos(pi/4) + 2*sin(pi/4)*cos(x),
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
  have : cos(2*x)  =  -sin(x)**2 + cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : -sin(x)**2 + cos(x)**2  =  (-sin(x) + cos(x))*(sin(x) + cos(x)),
  {
  ring_exp,
  },
  rw this,
  have : sin(-x + pi/4)  =  -sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
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
  have : (-sin(x) + cos(x))*(sin(x) + cos(x))/(-sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x)) =  sqrt(2)*(sin(x) + cos(x)),
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
  have : 2*sin(x)*(sqrt(2)/2) + 2*(sqrt(2)/2)*cos(x)  =  sqrt(2)*(sin(x) + cos(x)),
  {
  ring_exp,
  },
  rw this,
  norm_num,
end

lemma Trigo_5_369_EPCK (h0 : cos(pi/6) ≠ 0) (h1 : cos(pi/4) ≠ 0) (h2 : sin(pi/12) ≠ 0) (h3: cos(pi/18) ≠ 0) (h4 : 2 - sqrt(3) ≠ 0) : (sin(pi/18)*sin(pi/12) + sin(13*pi/36))/(sin(5*pi/36) - cos(pi/12)*cos(4*pi/9))=2+sqrt(3):=
begin
  have : sin(13*pi/36)  =  cos(5*pi/36),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(5*pi/36)  =  -sin(pi/18)*sin(pi/12) + cos(pi/18)*cos(pi/12),
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
  have : cos(4*pi/9)  =  sin(pi/18),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(5*pi/36)  =  sin(pi/18)*cos(pi/12) + sin(pi/12)*cos(pi/18),
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
  have : cos (π / 18) * (cos (π / 12) * (sin (π / 12) * cos (π / 18))⁻¹) = cos(pi/12)/sin(pi/12),
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

lemma Trigo_5_370_SXDW : sin(x - y)*sin(x + y) - cos(x - y)*cos(x + y)=-cos(2*x):=
begin
  have : sin(x - y)  =  sin(x)*cos(y) - cos(x)*sin(y),
  {
  have : sin(x-y) = sin((x) - (y)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_sub,
  },
  rw this,
  have : sin(x + y)  =  sin(x)*cos(y) + cos(x)*sin(y),
  {
  have : sin(x+y) = sin((x) + (y)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_add,
  },
  rw this,
  have : (sin(x)*cos(y) - cos(x)*sin(y))*(sin(x)*cos(y) + cos(x)*sin(y))  =  sin(x)**2*cos(y)**2 -sin(y)**2*cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  have : cos(x - y)  =  cos(x)*cos(y) + sin(x)*sin(y),
  {
  have : cos(x-y) = cos((x) - (y)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  },
  rw this,
  have : cos(x + y)  =  cos(x)*cos(y) - sin(x)*sin(y),
  {
  have : cos(x+y) = cos((x) + (y)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  },
  rw this,
  have : (cos(x)*cos(y) + sin(x)*sin(y))*(cos(x)*cos(y) - sin(x)*sin(y))  =  cos(x)**2*cos(y)**2 - sin(x)**2*sin(y)**2,
  {
  ring_exp,
  },
  rw this,
  have : sin(x)**2*cos(y)**2 - sin(y)**2*cos(x)**2 - (cos(x)**2*cos(y)**2 - sin(x)**2*sin(y)**2) = sin(x)**2*cos(y)**2 + sin(x)**2*sin(y)**2 - sin(y)**2*cos(x)**2 - cos(x)**2*cos(y)**2,
  {
  ring,
  },
  rw this,
  have : sin(x)**2*cos(y)**2 + sin(x)**2*sin(y)**2  =  sin(x)**2*(sin(y)**2 + cos(y)**2),
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
  have : sin(y)**2*cos(x)**2 + cos(x)**2*cos(y)**2  =  cos(x)**2*(sin(y)**2 + cos(y)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  simp,
  have : cos(2*x) = -sin(x)**2 + cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  linarith,
end

lemma Trigo_5_371_UQCA (h0 : sin(2*pi/9) ≥ 0) (h1 : sin(2*pi/9) ≠ 0) : (sqrt(3)*sin(pi/18) + cos(pi/18))/sqrt(1 - cos(4*pi/9))=sqrt(2):=
begin
  have : sqrt(3)*sin(pi/18)  =  2*sin(pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18)  =  2*sin(2*pi/9),
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
  have : cos(4*pi/9)  =  -sin(2*pi/9)**2 + cos(2*pi/9)**2,
  {
  have : cos (4*pi/9) = cos(2*(2*pi/9)),
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
  have : 1 - (-sin(2*π/9)**2 + (1 - sin(2*π/9)**2)) = 2*sin(2*pi/9)**2,
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

lemma Trigo_5_372_DLNH (h0 : -cos 1 + sin 1 ≥ 0) (h1 : cos 1 ≥ 0) (h2 : 0 ≤ 2) : 2*sqrt(1 - sin(2)) + sqrt(2*cos(2) + 2)=2*sin(1):=
begin
  have : 1 - sin(2)  =  sin(1)**2 + cos(1)**2 - sin(2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(2)  =  2*sin(1)*cos(1),
  {
  have : sin (2) = sin(2*(1)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(1)**2 + cos(1)**2 - 2*sin(1)*cos(1)  =  (-cos(1) + sin(1))**2,
  {
  ring_exp,
  },
  rw this,
  have : 2*cos(2) + 2  =  4*cos(1)**2,
  {
  have : cos(1)**2 = cos(2)/2 + 1/2,
  {
  have : cos (2) = cos(2*(1)),
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

lemma Trigo_5_373_AGWJ (h0 : sin(pi/7) ≠ 0) : cos(2*pi/7) + cos(4*pi/7) + cos(6*pi/7)=-1/2:=
begin
  have : cos(2*pi/7) + cos(4*pi/7) + cos(6*pi/7)  =  (2*sin(pi/7)*cos(6*pi/7) + 2*sin(pi/7)*cos(4*pi/7) + 2*sin(pi/7)*cos(2*pi/7))/(2*sin(pi/7)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : 2*sin(pi/7)*cos(6*pi/7)  =  sin(-5*pi/7) + sin(pi),
  {
  have : sin(pi/7)*cos(6*pi/7) = sin(-5*pi/7)/2 + sin(pi)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/7) + (6*pi/7)) = sin (pi),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/7) - (6*pi/7)) = sin (-5*pi/7),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : 2*sin(pi/7)*cos(4*pi/7)  =  sin(-3*pi/7) + sin(5*pi/7),
  {
  have : sin(pi/7)*cos(4*pi/7) = sin(-3*pi/7)/2 + sin(5*pi/7)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/7) + (4*pi/7)) = sin (5*pi/7),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/7) - (4*pi/7)) = sin (-3*pi/7),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : 2*sin(pi/7)*cos(2*pi/7)  =  sin(-pi/7) + sin(3*pi/7),
  {
  have : sin(pi/7)*cos(2*pi/7) = sin(-pi/7)/2 + sin(3*pi/7)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/7) + (2*pi/7)) = sin (3*pi/7),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/7) - (2*pi/7)) = sin (-pi/7),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : sin(-3*pi/7)  =  -sin(3*pi/7),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-3*pi/7) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-5*pi/7)  =  -sin(5*pi/7),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/7) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-pi/7)  =  -sin(pi/7),
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

lemma Trigo_5_374_VVQR (h0 : cos(4*pi/9) ≠ 0) (h1 : cos(2*pi/9) ≠ 0) (h2 : 1 - tan(2*pi/9) * tan(4*pi/9) ≠ 0) : -sqrt(3)*tan(2*pi/9)*tan(4*pi/9) + tan(2*pi/9) + tan(4*pi/9)=-sqrt(3):=
begin
  rw add_assoc,
  have : tan(2*pi/9) + tan(4*pi/9)  =  (-tan(2*pi/9)*tan(4*pi/9) + 1)*tan(2*pi/3),
  {
  rw tan_add_tan,
  have : tan((2*pi/9) + (4*pi/9)) = tan (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : tan(2*pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : (-tan(2*pi/9)*tan(4*pi/9) + 1)*-tan(pi/3)  =  tan(2*pi/9)*tan(pi/3)*tan(4*pi/9) - tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
  ring_exp,
end

lemma Trigo_5_375_EZCK (h0 : cos(pi/10) ≠ 0) (h1 : 1 - tan(pi/10) * tan(pi/15) ≠ 0) (h2 : cos(pi/15) ≠ 0) : tan(pi/15)*tan(pi/10) + sqrt(3)*tan(pi/15) + sqrt(3)*tan(pi/10)=1:=
begin
  rw add_assoc,
  have : sqrt(3)*tan(pi/15) + sqrt(3)*tan(pi/10)  =  sqrt(3)*(tan(pi/15) + tan(pi/10)),
  {
  ring_exp,
  },
  rw this,
  have : tan(pi/15) + tan(pi/10)  =  (-tan(pi/15)*tan(pi/10) + 1)*tan(pi/6),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((pi/10) + (pi/15)) = tan (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(pi/15)*tan(pi/10) + 1)*tan(pi/6)  =  -tan(pi/15)*tan(pi/10)*tan(pi/6) + tan(pi/6),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_six,
  have : sqrt(3)*(-tan(π/15)*tan(π/10)*(sqrt(3)/3) + sqrt(3)/3)  =  -tan(pi/15)*tan(pi/10) + 1,
  {
  ring_exp,
  rw sq_sqrt,
  ring_exp,
  linarith,
  },
  rw this,
  norm_num,
end

lemma Trigo_5_376_SNED (h0 : cos(pi/4) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : -sin(x) + cos(x) ≠ 0) (h3 : sin(2*x) + 1 ≠ 0) : cos(2*x)*tan(x + pi/4)/(2*cos(-x + pi/4)**2)=1:=
begin
  have : tan(x + pi/4)  =  (tan(x) + tan(pi/4))/(-tan(pi/4)*tan(x) + 1),
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
  have : sin(x)/cos(x) + 1  =  (sin(x) + cos(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : -1*(sin(x)/cos(x)) + 1  =  (-sin(x) + cos(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : cos(2*x)  =  -sin(x)**2 + cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : -sin(x)**2 + cos(x)**2  =  (-sin(x) + cos(x))*(sin(x) + cos(x)),
  {
  ring_exp,
  },
  rw this,
  have : 2*cos(-x + pi/4)**2  =  cos(-2*x + pi/2) + 1,
  {
  have : cos(-x + pi/4)**2 = cos(-2*x + pi/2)/2 + 1/2,
  {
  have : cos (-2*x + pi/2) = cos(2*(-x + pi/4)),
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
  have : cos(-2*x + pi/2)  =  sin(2*x),
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
  have : (sin(x) + cos(x))**2  =  sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  have : 2*sin(x)*cos(x)  =  sin(2*x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  field_simp,
  left,
  ring_exp,
end

lemma Trigo_5_377_VMLJ (h0 : sin(pi/5) ≠ 0) : cos(pi/5)*cos(2*pi/5)=1/4:=
begin
  have : cos(pi/5)  =  sin(2*pi/5)/(2*sin(pi/5)),
  {
  have : sin (2*pi/5) = sin(2*(pi/5)),
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
  have : sin(2*pi/5)*cos(2*pi/5)  =  sin(4*pi/5)/2,
  {
  have : sin(4*pi/5) = 2*sin(2*pi/5)*cos(2*pi/5),
  {
  have : sin (4*pi/5) = sin(2*(2*pi/5)),
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
  have : sin(4*pi/5)  =  sin(pi/5),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (4*pi/5) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_5_378_LZPJ (h0 : tan(31*pi/90) ≠ 0) : sin(pi/5)**2 + sin(3*pi/10)**2 + tan(7*pi/45)*tan(pi/4)*tan(31*pi/90)=2:=
begin
  have : sin(pi/5)**2  =  1/2 - cos(2*pi/5)/2,
  {
  have : cos (2*pi/5) = cos(2*(pi/5)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : sin(3*pi/10)**2  =  1/2 - cos(3*pi/5)/2,
  {
  have : cos (3*pi/5) = cos(2*(3*pi/10)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(3*pi/5)  =  -cos(2*pi/5),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/5) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(7*pi/45)  =  1/tan(31*pi/90),
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

lemma Trigo_5_379_PLEF (h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/18) ≠ 0) : (tan(pi/18) - sqrt(3))*cos(5*pi/18)=-1:=
begin
  have : sqrt(3)  =  tan(pi/3),
  {
  field_simp,
  },
  rw this,
  rw sub_eq_neg_add,
  have : -tan(pi/3) + tan(pi/18)  =  sin(-5*pi/18)/(cos(pi/18)*cos(pi/3)),
  {
  rw neg_add_eq_sub,
  rw tan_sub_tan',
  have : sin((pi/18) - (pi/3)) = sin (-5*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  repeat {assumption},
  },
  rw this,
  have : sin(-5*pi/18)  =  -sin(5*pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw div_mul_eq_mul_div,
  have : -sin(5*pi/18)*cos(5*pi/18)  =  -sin(5*pi/9)/2,
  {
  have : sin(5*pi/9) = 2*sin(5*pi/18)*cos(5*pi/18),
  {
  have : sin (5*pi/9) = sin(2*(5*pi/18)),
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
  have : sin(5*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
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

lemma Trigo_5_380_ZVBA (h0 : cos(x)**2 ≠ 0) (h1 : cos(x) ≠ 0) : (1 - cos(2*x))/(cos(2*x) + 1)=tan(x)**2:=
begin
  have : cos(2*x)  =  -sin(x)**2 + cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
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

lemma Trigo_5_381_UFKP (h0 : cos(x/2) ≠ 0) (h1 : sin(x/2) ≠ 0) (h2 : cos(x) ≠ 0) : cos(x)**2/(-tan(x/2) + 1/tan(x/2))=1/4*sin(2*x):=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : -(sin(x/2)/cos(x/2)) + cos(x/2)/sin(x/2)  =  (-sin(x/2)**2 + cos(x/2)**2)/(sin(x/2)*cos(x/2)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : -sin(x/2)**2 + cos(x/2)**2  =  cos(x),
  {
  have : cos (x) = cos(2*(x/2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(x/2)*cos(x/2)  =  sin(x)/2,
  {
  have : sin(x) = 2*sin(x/2)*cos(x/2),
  {
  have : sin (x) = sin(2*(x/2)),
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
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_5_382_HMEV (h0 : cos(pi/3) ≠ 0) (h1 : 1 + tan(pi/3) * tan(pi/18) ≠ 0) (h2 : cos(pi/18) ≠ 0) (h3 : tan(5*π/18) ≠ 0) : (-tan(pi/18) + sqrt(3))*tan(2*pi/9) - sqrt(3)*tan(pi/18)=1:=
begin
  have : sqrt(3)  =  tan(pi/3),
  {
  field_simp,
  },
  rw this,
  have : -tan(pi/18) + tan(pi/3)  =  (tan(pi/18)*tan(pi/3) + 1)*tan(5*pi/18),
  {
  rw neg_add_eq_sub,
  rw tan_sub_tan,
  have : tan((pi/3) - (pi/18)) = tan (5*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : tan(2*pi/9)  =  1/tan(5*pi/18),
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

lemma Trigo_5_383_OJSQ (h0 : cos(pi/4) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : -sin(x) + cos(x) ≠ 0) : cos(2*x)/tan(-x + pi/4)=1+sin(2*x):=
begin
  have : tan(-x + pi/4)  =  (-tan(x) + tan(pi/4))/(tan(pi/4)*tan(x) + 1),
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
  have : 1*(sin(x)/cos(x)) + 1  =  (sin(x) + cos(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : -(sin(x)/cos(x)) + 1  =  (-sin(x) + cos(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : cos(2*x)  =  -sin(x)**2 + cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : -sin(x)**2 + cos(x)**2  =  (-sin(x) + cos(x))*(sin(x) + cos(x)),
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
  have : (sin(x) + cos(x))**2  =  sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x),
  {
  ring_exp,
  },
  rw this,
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  field_simp,
  ring_exp,
end

lemma Trigo_5_384_HVMF (h0 : cos(x + pi/6) ≠ 0) (h1 : cos(-x + pi/6) ≠ 0) (h2 : 1 - tan(x + pi/6) * tan(-x + pi/6) ≠ 0) : sqrt(3)*tan(-x + pi/6)*tan(x + pi/6) + tan(-x + pi/6) + tan(x + pi/6)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(-x + pi/6) + tan(x + pi/6)  =  (-tan(-x + pi/6)*tan(x + pi/6) + 1)*tan(pi/3),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((x + pi/6) + (-x + pi/6)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(-x + pi/6)*tan(x + pi/6) + 1)*tan(pi/3)  =  -tan(pi/3)*tan(-x + pi/6)*tan(x + pi/6) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
end

lemma Trigo_5_385_SWHN (h0 : tan(pi/9) ≠ 0) (h1 : sin(pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0) : sqrt(3)*sin(pi/18)*tan(7*pi/18) + cos(pi/18)/tan(pi/9) - 2*cos(2*pi/9)=2:=
begin
  have : tan(7*pi/18)  =  1/tan(pi/9),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sqrt(3)*sin(pi/18)*(1/tan(pi/9)) + cos(pi/18)/tan(pi/9)  =  (sqrt(3)*sin(pi/18) + cos(pi/18))/tan(pi/9),
  {
  ring_exp,
  },
  rw this,
  have : sqrt(3)*sin(pi/18)  =  2*sin(pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18)  =  2*sin(2*pi/9),
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
  have : sin(2*pi/9)  =  2*sin(pi/9)*cos(pi/9),
  {
  have : sin (2*pi/9) = sin(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : 2*cos(2*pi/9)  =  2*cos(pi/9)**2 - 2*sin(pi/9)**2,
  {
  have : cos(2*pi/9) = -sin(pi/9)**2 + cos(pi/9)**2,
  {
  have : cos (2*pi/9) = cos(2*(pi/9)),
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
  have : 2*(2*sin(π/9)*cos(π/9))/(sin(π/9)/cos(π/9)) = 4*cos(pi/9)**2,
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

lemma Trigo_5_386_TYJS (h0 : 2 ≠ 0) : sin(x)**2 - sin(x)*cos(-x + pi/6) + cos(-x + pi/6)**2=3/4:=
begin
  have : cos(-x + pi/6)  =  sin(pi/6)*sin(x) + cos(pi/6)*cos(x),
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
  have : (sin(pi/6)*sin(x) + cos(pi/6)*cos(x))**2  =  sin(pi/6)**2*sin(x)**2 + 2*sin(pi/6)*sin(x)*cos(pi/6)*cos(x) + cos(pi/6)**2*cos(x)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  have : sin(x)*(1/2*sin(x) + sqrt(3)/2*cos(x))  =  sin(x)**2/2 + sqrt(3)*sin(x)*cos(x)/2,
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

lemma Trigo_5_387_DCTK : -sin(4*pi/5)*cos(29*pi/30) + sin(29*pi/30)*cos(4*pi/5)=1/2:=
begin
  have : -sin(4*pi/5)*cos(29*pi/30) + sin(29*pi/30)*cos(4*pi/5)  =  sin(pi/6),
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

lemma Trigo_5_388_APKQ : sin(13*pi/180)*cos(43*pi/180) - sin(43*pi/180)*cos(13*pi/180)=-1/2:=
begin
  rw sub_eq_neg_add,
  rw ← neg_mul,
  have : -sin(43*pi/180)*cos(13*pi/180) + sin(13*pi/180)*cos(43*pi/180)  =  sin(-pi/6),
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
  have : sin(-pi/6)  =  -sin(pi/6),
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

lemma Trigo_5_389_KLXX (h0 : cos(pi/5) ≠ 0) (h1 : cos(2*pi/15) ≠ 0) (h2 : 1 - tan(pi/5) * tan(2*pi/15) ≠ 0) : sqrt(3)*tan(2*pi/15)*tan(pi/5) + tan(2*pi/15) + tan(pi/5)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(2*pi/15) + tan(pi/5)  =  (-tan(2*pi/15)*tan(pi/5) + 1)*tan(pi/3),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((pi/5) + (2*pi/15)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(2*pi/15)*tan(pi/5) + 1)*tan(pi/3)  =  -tan(2*pi/15)*tan(pi/5)*tan(pi/3) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
  ring_exp,
end

lemma Trigo_5_390_CVUX (h0 : sin(5*pi/18) ≥ 0) (h1 : cos(5*pi/18) ≥ 0) : -sqrt(1 - cos(5*pi/9)) + sqrt(cos(5*pi/9) + 1)=-2*sin(pi/36):=
begin
  have : cos(5*pi/9)  =  -sin(5*pi/18)**2 + cos(5*pi/18)**2,
  {
  have : cos (5*pi/9) = cos(2*(5*pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : 1 - (-sin(5*π/18)**2 + cos(5*π/18)**2)  = (sin(5*pi/18)**2 + cos(5*pi/18)**2) - (-sin(5*π/18)**2 + cos(5*π/18)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : (sin(5*pi/18)**2 + cos(5*pi/18)**2) - (-sin(5*π/18)**2 + cos(5*π/18)**2) = 2*sin(5*pi/18)**2,
  {
  ring,
  },
  rw this,
  rw sqrt_mul,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  rw sin_sq,
  have : -(1-cos(5*π/18)**2) + cos(5*π/18)**2 + 1 = 2*cos(5*pi/18)**2,
  {
  ring,
  },
  rw this,
  rw sqrt_mul,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h1,
  have : sin(5*pi/18)  =  sqrt(2)*cos(pi/4)*sin(5*pi/18),
  {
  field_simp,
  },
  rw this,
  have : cos(5*pi/18)  =  sqrt(2)*sin(pi/4)*cos(5*pi/18),
  {
  field_simp,
  },
  rw this,
  ring_exp,
  rw sq_sqrt,
  have : 2*(cos(π/4)*-sin(5*π/18)) + 2*(sin(π/4)*cos(5*π/18)) = -2*sin(5*pi/18)*cos(pi/4) + 2*sin(pi/4)*cos(5*pi/18),
  {
  ring,
  },
  rw this,
  have : -2*sin(5*pi/18)*cos(pi/4) + 2*sin(pi/4)*cos(5*pi/18)  =  2*sin(-pi/36),
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
  have : sin(-pi/36)  =  -sin(pi/36),
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

lemma Trigo_5_391_NULQ (h0 : cos(pi/180) ≠ 0) (h1 : cos(11*pi/45) ≠ 0) (h2 : 1 - tan(pi/180) * tan(11*pi/45) ≠ 0) : (tan(pi/180) + 1)*(tan(11*pi/45) + 1)=2:=
begin
  have : (tan(pi/180) + 1)*(tan(11*pi/45) + 1)  =  tan(pi/180)*tan(11*pi/45) + tan(pi/180) + tan(11*pi/45) + 1,
  {
  ring_exp,
  },
  rw this,
  have : tan(π/180)*tan(11*π/45) + tan(π/180) + tan(11*π/45) = tan(π/180)*tan(11*π/45) + (tan(π/180) + tan(11*π/45)),
  {
  ring,
  },
  rw this,
  have : tan(pi/180) + tan(11*pi/45)  =  (-tan(pi/180)*tan(11*pi/45) + 1)*tan(pi/4),
  {
  rw tan_add_tan,
  have : tan((pi/180) + (11*pi/45)) = tan (pi/4),
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

lemma Trigo_5_392_ZNUK (h0 : 1 - tan(pi/10) * tan(7*pi/30) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : cos(7*pi/30) ≠ 0) : sqrt(3)*tan(pi/10)*tan(7*pi/30) + tan(pi/10) + tan(7*pi/30)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(pi/10) + tan(7*pi/30)  =  (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((pi/10) + (7*pi/30)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3)  =  -tan(pi/10)*tan(7*pi/30)*tan(pi/3) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
  ring_exp,
end

lemma Trigo_5_393_MLNR (h0 : 1+tan(pi/9)*tan(5*pi/18) ≠ 0) (h1 : cos(5*pi/18) ≠ 0) (h2 : tan((pi/9)-(5*pi/18)) ≠ 0) (h3 : cos(pi/9) ≠ 0) (h4 : cos(5*pi/18) ≠ 0) (h5 : tan(pi/9) - tan(5*pi/18) ≠ 0) (h6 : sqrt(3) ≠ 0) : (tan(-5*pi/18)*tan(pi/9) - 1)/(tan(pi/9) - tan(5*pi/18))=sqrt(3):=
begin
  have : tan(-5*pi/18)  =  -tan(5*pi/18),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw neg_mul,
  rw mul_comm,
  have : tan(pi/9)*tan(5*pi/18)  =  -1 + (-tan(5*pi/18) + tan(pi/9))/tan(-pi/6),
  {
  rw tan_mul_tan,
  have : tan((pi/9) - (5*pi/18)) = tan (-pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : tan(-pi/6)  =  -tan(pi/6),
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

lemma Trigo_5_394_RKYM : 2*sin(x)**4 + 3*sin(2*x)**2/4 + 5*cos(x)**4 - cos(x)*cos(3*x)=2*(1+cos(x)**2):=
begin
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  rw this,
  have : cos(3*x)  =  4*cos(x)**3 - 3*cos(x),
  {
  have : cos (3*x) = cos(3*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_three_mul,
  },
  rw this,
  have : cos(x)*(4*cos(x)**3 - 3*cos(x))  =  4*cos(x)**4 - 3*cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  have : 2*sin(x)**4 + 3*(2*sin(x)*cos(x))**2/4 + 5*cos(x)**4 - (4*cos(x)**4 - 3*cos(x)**2) = 2*sin(x)**4 + 3*sin(x)**2*cos(x)**2 + cos(x)**4 + 3*cos(x)**2,
  {
  ring,
  },
  rw this,
  have : 2*sin(x)**4 + 3*sin(x)**2*cos(x)**2 + cos(x)**4  =  (sin(x)**2 + cos(x)**2)*(2*sin(x)**2 + cos(x)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  ring_exp,
  rw sin_sq,
  ring_exp,
end

lemma Trigo_5_395_KSOQ (h0 : sin(pi/9) ≠ 0) : sin(pi/18)*sin(pi/6)*sin(5*pi/18)*sin(7*pi/18)=1/16:=
begin
  have : sin(pi/18)  =  cos(4*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(5*pi/18)  =  cos(2*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(7*pi/18)  =  cos(pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/9)  =  sin(2*pi/9)/(2*sin(pi/9)),
  {
  have : sin (2*pi/9) = sin(2*(pi/9)),
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
  have : cos(4*π/9)*sin(π/6)*cos(2*π/9)*(sin(2*π/9)/(2*sin(π/9))) = sin(2*π/9)*cos(2*π/9)*cos(4*π/9)*sin(π/6)/(2*sin(π/9)),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/9)*cos(2*pi/9)  =  sin(4*pi/9)/2,
  {
  have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
  {
  have : sin (4*pi/9) = sin(2*(2*pi/9)),
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
  have : sin(4*π/9)/2*cos(4*π/9) = sin(4*π/9)*cos(4*π/9)/2,
  {
  ring,
  },
  rw this,
  have : sin(4*pi/9)*cos(4*pi/9)  =  sin(8*pi/9)/2,
  {
  have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
  {
  have : sin (8*pi/9) = sin(2*(4*pi/9)),
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
  have : sin(8*pi/9)  =  sin(pi/9),
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

lemma Trigo_5_396_SLLC : sin(pi/9)**2 + sin(pi/9)*cos(5*pi/18) + sin(2*pi/9)**2=3/4:=
begin
  have : sin(pi/9)**2  =  1/2 - cos(2*pi/9)/2,
  {
  have : cos (2*pi/9) = cos(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : sin(2*pi/9)**2  =  1/2 - cos(4*pi/9)/2,
  {
  have : cos (4*pi/9) = cos(2*(2*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : 1/2 - cos(2*π/9)/2 + sin(π/9)*cos(5*π/18) + (1/2 - cos(4*π/9)/2) = -cos(2*π/9)/2 - cos(4*π/9)/2 + sin(π/9)*cos(5*π/18) + 1,
  {
  ring,
  },
  rw this,
  have : -cos(2*pi/9)/2 - cos(4*pi/9)/2  =  -cos(pi/9)*cos(pi/3),
  {
  have : cos(2*pi/9) + cos(4*pi/9) = 2*cos(pi/9)*cos(pi/3),
  {
  rw add_comm,
  rw cos_add_cos,
  have : cos(((4*pi/9) + (2*pi/9))/2) = cos (pi/3),
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
  have : sin(pi/9)*cos(5*pi/18)  =  sin(-pi/6)/2 + sin(7*pi/18)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/9) + (5*pi/18)) = sin (7*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/9) - (5*pi/18)) = sin (-pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : sin(-pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/6)  =  cos(pi/3),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(7*pi/18)  =  cos(pi/9),
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

lemma Trigo_5_397_YLLO (h0 : -cos(pi/18) + sin(pi/18) ≤ 0) (h1 : -sin(π/18) + cos(π/18) ≠ 0) (h2 : sin(11*pi/36) ≠ 0) : cos(pi/9)/(sqrt(1 - sin(pi/9))*cos(7*pi/36))=sqrt(2):=
begin
  have : sin(pi/9)  =  2*sin(pi/18)*cos(pi/18),
  {
  have : sin (pi/9) = sin(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 1 - 2*sin(π/18)*cos(π/18) = sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(π/18)*cos(π/18),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(pi/18)**2 + cos(pi/18)**2 - 2*sin(π/18)*cos(π/18)  =  (-cos(pi/18) + sin(pi/18))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h0,
  have : cos(pi/9)  =  -sin(pi/18)**2 + cos(pi/18)**2,
  {
  have : cos (pi/9) = cos(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : -sin(pi/18)**2 + cos(pi/18)**2  =  (-sin(pi/18) + cos(pi/18))*(sin(pi/18) + cos(pi/18)),
  {
  ring_exp,
  },
  rw this,
  have : sin(pi/18) + cos(pi/18)  =  sqrt(2)*(sqrt(2)*sin(pi/18)/2 + sqrt(2)*cos(pi/18)/2),
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
  have : sqrt(2)*sin(pi/18)/2  =  sin(pi/18)*cos(pi/4),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sqrt(2)*cos(pi/18)/2  =  sin(pi/4)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : sin(pi/18)*cos(pi/4) + sin(pi/4)*cos(pi/18)  =  sin(11*pi/36),
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
  have : cos(7*pi/36)  =  sin(11*pi/36),
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

lemma Trigo_5_398_VGEE (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(x + pi/2)*sin(x + pi)*tan(x + 3*pi)/(sin(-x)*cos(x + 3*pi/2))=1:=
begin
  have : sin(x + pi/2)  =  cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x + pi)  =  -sin(x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(x + 3*pi)  =  tan(x),
  {
  rw tan_eq_tan_add_int_mul_pi (x + 3*pi) (-3),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(-x)  =  -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x + 3*pi/2)  =  sin(x),
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

lemma Trigo_5_399_NEPM (h0 : cos(x) ≠ 0) (h1 : 1 - cos(x)**2 ≠ 0) : (-sin(x)**4 - cos(x)**4 + 1)/(-sin(x)**4 + sin(x)**2)=2:=
begin
  have : -sin(x)**4 - cos(x)**4  =  (-sin(x)**2 - cos(x)**2)*(sin(x)**2 + cos(x)**2) + 2*sin(x)**2*cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  have : -sin(x)**2 - cos(x)**2  =  -1,
  {
  have : sin(x)**2 + cos(x)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
  },
  rw this,
  have : -sin(x)**4 + sin(x)**2  =  (1 - sin(x)**2)*sin(x)**2,
  {
  ring_exp,
  },
  rw this,
  rw sin_sq,
  norm_num,
  field_simp,
  ring_exp,
end