// SVA checker for barrel_shifter (4-bit rotate barrel shifter)
// Assumes: dir==1 -> rotate left by shift_amt; dir==0 -> rotate right by shift_amt
// Bind this to the DUT and drive clk/rst_n from the TB.

module barrel_shifter_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  in,
  input  logic [1:0]  shift_amt,
  input  logic        dir,
  input  logic [3:0]  out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic [3:0] rotl4 (input [3:0] v, input [1:0] k);
    case (k)
      2'd0: rotl4 = v;
      2'd1: rotl4 = {v[2:0], v[3]};
      2'd2: rotl4 = {v[1:0], v[3:2]};
      default: rotl4 = {v[0], v[3:1]}; // k==3
    endcase
  endfunction

  function automatic [3:0] rotr4 (input [3:0] v, input [1:0] k);
    case (k)
      2'd0: rotr4 = v;
      2'd1: rotr4 = {v[0], v[3:1]};
      2'd2: rotr4 = {v[1:0], v[3:2]};
      default: rotr4 = {v[2:0], v[3]}; // k==3
    endcase
  endfunction

  // No X/Z on out when inputs are known
  assert property (!$isunknown({in,shift_amt,dir}) |-> !$isunknown(out))
    else $error("barrel_shifter: out has X/Z with known inputs");

  // Golden functional check
  assert property (dir ? (out == rotl4(in, shift_amt))
                       : (out == rotr4(in, shift_amt)))
    else $error("barrel_shifter: mismatch out vs expected rotate");

  // Passthrough for shift_amt==0
  assert property (shift_amt == 2'd0 |-> out == in)
    else $error("barrel_shifter: shift_amt==0 must pass through");

  // Functional coverage: all dir/shift_amt combos observed with correct out
  cover property (shift_amt==2'd0 && out==in);
  cover property ( dir && shift_amt==2'd1 && out=={in[2:0],in[3]});
  cover property ( dir && shift_amt==2'd2 && out=={in[1:0],in[3:2]});
  cover property ( dir && shift_amt==2'd3 && out=={in[0],in[3:1]});
  cover property (!dir && shift_amt==2'd1 && out=={in[0],in[3:1]});
  cover property (!dir && shift_amt==2'd2 && out=={in[1:0],in[3:2]});
  cover property (!dir && shift_amt==2'd3 && out=={in[2:0],in[3]});

  // Stimulus coverage for representative input patterns
  cover property (in==4'h0);
  cover property (in==4'hF);
  cover property (in==4'h1);
  cover property (in==4'h8);
  cover property (in==4'h5);
  cover property (in==4'hA);

endmodule

// Bind example (replace tb_clk/tb_rst_n with your TB signals)
// bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .in(in), .shift_amt(shift_amt), .dir(dir), .out(out)
// );