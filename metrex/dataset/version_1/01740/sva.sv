// SVA bind module for multiplier_8bit
module multiplier_8bit_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic        ctrl,
  input logic [15:0] c
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Expected product (16-bit)
  let exp_prod = ctrl
                 ? logic [15:0]'($signed(a)   * $signed(b))
                 : logic [15:0]'($unsigned(a) * $unsigned(b));

  // Inputs known -> output known
  a_no_x:       assert property (!$isunknown({a,b,ctrl}));
  c_no_x_known: assert property (!$isunknown({a,b,ctrl}) |-> !$isunknown(c));

  // Functional correctness (same-cycle, combinational)
  correct_prod: assert property (!$isunknown({a,b,ctrl}) |-> c == exp_prod)
                  else $error("mul mismatch a=%0h b=%0h ctrl=%0b c=%0h exp=%0h",
                               a, b, ctrl, c, exp_prod);

  // Combinational stability: if inputs stable, output stable
  stable_out:   assert property ($stable({a,b,ctrl}) |-> $stable(c));

  // Basic mode coverage
  cover_unsigned_mode: cover property (! $isunknown({a,b,ctrl}) && (ctrl==0));
  cover_signed_mode:   cover property (! $isunknown({a,b,ctrl}) && (ctrl==1));

  // Corner-case functional coverage
  // Unsigned: max*max and zero cases
  cover_u_max:  cover property (ctrl==0 && a==8'hFF && b==8'hFF && c==16'hFE01);
  cover_u_zero: cover property (ctrl==0 && (a==8'h00 || b==8'h00) && c==16'h0000);

  // Signed: min/neg/pos mixes and identities
  cover_s_min_pos:  cover property (ctrl==1 && a==8'h80 && b==8'h01 && c==16'hFF80); // -128*+1=-128
  cover_s_min_neg1: cover property (ctrl==1 && a==8'h80 && b==8'hFF && c==16'h0080); // -128*-1=+128
  cover_s_neg_neg:  cover property (ctrl==1 && a==8'hFF && b==8'hFF && c==16'h0001); // -1*-1=+1
  cover_s_neg_pos:  cover property (ctrl==1 && a==8'hFF && b==8'h01 && c==16'hFFFF); // -1*+1=-1
  cover_s_zero:     cover property (ctrl==1 && (a==8'h00 || b==8'h00) && c==16'h0000);

  // Mode toggle with stable operands
  cover_ctrl_rise: cover property ($rose(ctrl) && $stable({a,b}));
  cover_ctrl_fall: cover property ($fell(ctrl) && $stable({a,b}));
endmodule

// Bind example (connect clk/rst_n from your environment)
bind multiplier_8bit multiplier_8bit_sva u_multiplier_8bit_sva (
  .clk   (clk),
  .rst_n (rst_n),
  .a     (a),
  .b     (b),
  .ctrl  (ctrl),
  .c     (c)
);