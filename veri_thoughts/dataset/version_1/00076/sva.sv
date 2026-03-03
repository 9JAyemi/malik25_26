// SVA for barrel_shifter
module barrel_shifter_sva
(
  input logic [3:0] A,
  input logic [1:0] shift_amount,
  input logic       shift_dir,
  input logic [3:0] Y
);
  logic [3:0] exp_left, exp_right;
  always_comb begin
    exp_left  = (A << shift_amount) & 4'hF;
    exp_right = (A >> shift_amount);

    assert (!$isunknown({A,shift_amount,shift_dir}))
      else $error("barrel_shifter: X/Z on inputs");

    assert (shift_dir ? (Y == exp_left) : (Y == exp_right))
      else $error("barrel_shifter: Y mismatch A=%0h sa=%0d dir=%0b Y=%0h expL=%0h expR=%0h",
                  A, shift_amount, shift_dir, Y, exp_left, exp_right);

    // Functional coverage of all shift_dir/shift_amount combinations
    cover (shift_dir==1'b1 && shift_amount==2'b00);
    cover (shift_dir==1'b1 && shift_amount==2'b01);
    cover (shift_dir==1'b1 && shift_amount==2'b10);
    cover (shift_dir==1'b1 && shift_amount==2'b11);
    cover (shift_dir==1'b0 && shift_amount==2'b00);
    cover (shift_dir==1'b0 && shift_amount==2'b01);
    cover (shift_dir==1'b0 && shift_amount==2'b10);
    cover (shift_dir==1'b0 && shift_amount==2'b11);
  end
endmodule

bind barrel_shifter barrel_shifter_sva bs_chk (
  .A(A), .shift_amount(shift_amount), .shift_dir(shift_dir), .Y(Y)
);


// SVA for decoder
module decoder_sva
(
  input logic       enable,
  input logic [1:0] select,
  input logic [15:0] out
);
  logic [15:0] exp;
  always_comb begin
    exp = enable ? (16'h0001 << select) : 16'h0000;

    assert (!$isunknown({enable,select}))
      else $error("decoder: X/Z on inputs");

    assert (out == exp)
      else $error("decoder: out mismatch en=%0b sel=%0d out=%h exp=%h",
                  enable, select, out, exp);

    assert ($onehot0(out)) else $error("decoder: out not onehot0");
    assert (out[15:4] == 12'h000) else $error("decoder: upper bits must be 0");

    // Coverage: disabled and all selects when enabled
    cover (enable==1'b0);
    cover (enable==1'b1 && select==2'b00);
    cover (enable==1'b1 && select==2'b01);
    cover (enable==1'b1 && select==2'b10);
    cover (enable==1'b1 && select==2'b11);
  end
endmodule

bind decoder decoder_sva dec_chk (
  .enable(enable), .select(select), .out(out)
);


// SVA for top_module (end-to-end composition)
module top_module_sva
(
  input  logic [3:0]  A,
  input  logic [1:0]  shift_amount,
  input  logic        shift_dir,
  input  logic        enable,
  input  logic [1:0]  select,
  input  logic [15:0] out
);
  logic [3:0]  bs_y;
  logic [3:0]  dec_lsb;
  logic [15:0] exp_out;
  always_comb begin
    bs_y     = shift_dir ? ((A << shift_amount) & 4'hF) : (A >> shift_amount);
    dec_lsb  = enable ? (4'h1 << select) : 4'h0;
    exp_out  = {bs_y, 12'h000} | {12'h000, dec_lsb};

    assert (!$isunknown({A,shift_amount,shift_dir,enable,select}))
      else $error("top: X/Z on inputs");

    assert (out[15:12] == bs_y)     else $error("top: upper nibble != shifted_A");
    assert (out[11:4]  == 8'h00)    else $error("top: middle bits not zero");
    assert (out[3:0]   == dec_lsb)  else $error("top: LSB nibble != decoder[3:0]");
    assert (out == exp_out)         else $error("top: out != expected composite");

    // A few cross covers
    cover (shift_dir==1 && shift_amount==2 && enable==1 && select==2);
    cover (shift_dir==0 && shift_amount==3 && enable==1 && select==3);
    cover (shift_dir==1 && shift_amount==0 && enable==0);
  end
endmodule

bind top_module top_module_sva top_chk (
  .A(A), .shift_amount(shift_amount), .shift_dir(shift_dir),
  .enable(enable), .select(select), .out(out)
);