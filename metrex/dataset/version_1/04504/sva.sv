// SVA for pdp1_opr_decoder
// Bind one of the assertion modules below to your DUT:
//   // PDP-1 behavior (default parameter)
//   bind pdp1_opr_decoder pdp1_opr_decoder_sva_base sva_base (.*,.r_pf_mask(r_pf_mask));
//   // PDP-1D behavior (swap/select + IO invert)
//   bind pdp1_opr_decoder pdp1_opr_decoder_sva_d     sva_d    (.*,.r_pf_mask(r_pf_mask));

module pdp1_opr_decoder_sva_common;
  // shared utility functions in a package-like module for reuse via static methods
  function automatic logic [0:18] extend19_18(input logic [0:17] v);
    extend19_18 = {1'b0, v};
  endfunction
  function automatic logic [0:18] extend19_6(input logic [0:5] v);
    extend19_6 = {13'b0, v};
  endfunction
  function automatic logic [0:17] trim18(input logic [0:18] v);
    trim18 = v[1:18];
  endfunction

  function automatic logic [0:18] f_ac_19(
      input logic [0:11] mask,
      input logic [0:17] ac,
      input logic [0:17] tw,
      input logic [0:5]  pf);
    logic [0:18] s4, s3, s2, s1;
    s4 = mask[4] ? 19'b0 : extend19_18(ac);
    s3 = mask[1] ? (s4 | extend19_18(tw)) : s4;
    s2 = mask[5] ? (s3 | extend19_6(pf))  : s3;
    s1 = mask[2] ? ~s2                   : s2;
    return s1;
  endfunction

  function automatic logic [0:18] f_io_base_19(
      input logic [0:11] mask,
      input logic [0:17] io);
    logic [0:18] s;
    s = mask[0] ? 19'b0 : extend19_18(io);
    return s;
  endfunction

  function automatic logic [0:18] f_io_d_19(
      input logic [0:11] mask,
      input logic [0:17] io,
      input logic        op_i);
    logic [0:18] b;
    b = f_io_base_19(mask, io);
    return op_i ? ~b : b;
  endfunction

  function automatic logic [0:5] f_pf_mask(input logic [0:2] sel);
    case (sel)
      3'b000: f_pf_mask = 6'b000000;
      3'b001: f_pf_mask = 6'b000001;
      3'b010: f_pf_mask = 6'b000010;
      3'b011: f_pf_mask = 6'b000100;
      3'b100: f_pf_mask = 6'b001000;
      3'b101: f_pf_mask = 6'b010000;
      3'b110: f_pf_mask = 6'b100000;
      default: f_pf_mask = 6'b111111;
    endcase
  endfunction
endmodule

module pdp1_opr_decoder_sva_base(
  input                op_i,
  input  logic [0:11]  op_mask,
  input  logic [0:17]  op_ac,
  input  logic [0:17]  op_io,
  input  logic [0:5]   op_pf,
  input  logic [0:17]  op_tw,
  input  logic [0:17]  op_r_ac,
  input  logic [0:17]  op_r_io,
  input  logic [0:5]   op_r_pf,
  input  logic [0:5]   r_pf_mask
);
  import pdp1_opr_decoder_sva_common::*;

  event comb_ev;
  always @(op_i or op_mask or op_ac or op_io or op_pf or op_tw) -> comb_ev;

  // Golden recompute
  function automatic logic [0:17] exp_ac(input logic [0:11] m, input logic [0:17] a, t, input logic [0:5] p);
    return trim18(f_ac_19(m,a,t,p));
  endfunction
  function automatic logic [0:17] exp_io(input logic [0:11] m, input logic [0:17] i);
    return trim18(f_io_base_19(m,i));
  endfunction
  function automatic logic [0:5] exp_pf(input logic [0:11] m, input logic [0:5] pf_in, input logic [0:5] pfmsk);
    if (|m[8:11]) begin
      exp_pf = m[8] ? (pf_in | pfmsk) : (pf_in & ~pfmsk);
    end else begin
      exp_pf = pf_in;
    end
  endfunction

  // No-X on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({op_mask,op_ac,op_io,op_pf,op_tw}))
    |-> !$isunknown({op_r_ac,op_r_io,op_r_pf});

  // AC and IO paths (PDP-1)
  assert property (@(comb_ev) op_r_ac === exp_ac(op_mask, op_ac, op_tw, op_pf));
  assert property (@(comb_ev) op_r_io === exp_io(op_mask, op_io));

  // PF mask decode and PF result
  assert property (@(comb_ev) r_pf_mask === f_pf_mask(op_mask[9:11]));
  assert property (@(comb_ev) op_r_pf === exp_pf(op_mask, op_pf, r_pf_mask));

  // Minimal functional coverage
  genvar b;
  generate
    for (b=0; b<=11; b++) begin : C_MASK_BITS
      cover property (@(comb_ev) op_mask[b]);
    end
  endgenerate
  // PF selector coverage
  cover property (@(comb_ev) op_mask[9:11]==3'b000);
  cover property (@(comb_ev) op_mask[9:11]==3'b001);
  cover property (@(comb_ev) op_mask[9:11]==3'b010);
  cover property (@(comb_ev) op_mask[9:11]==3'b011);
  cover property (@(comb_ev) op_mask[9:11]==3'b100);
  cover property (@(comb_ev) op_mask[9:11]==3'b101);
  cover property (@(comb_ev) op_mask[9:11]==3'b110);
  cover property (@(comb_ev) op_mask[9:11]==3'b111);
  cover property (@(comb_ev) (|op_mask[8:11]) &&  op_mask[8]); // OR case
  cover property (@(comb_ev) (|op_mask[8:11]) && !op_mask[8]); // AND-with-invert case
  // Key datapath features
  cover property (@(comb_ev) op_mask[1]);  // OR with TW
  cover property (@(comb_ev) op_mask[5]);  // OR with PF bits into AC
  cover property (@(comb_ev) op_mask[2]);  // complement AC path
  cover property (@(comb_ev) op_mask[0]);  // zero IO
  cover property (@(comb_ev) op_mask[4]);  // zero AC pre-OR
endmodule

module pdp1_opr_decoder_sva_d(
  input                op_i,
  input  logic [0:11]  op_mask,
  input  logic [0:17]  op_ac,
  input  logic [0:17]  op_io,
  input  logic [0:5]   op_pf,
  input  logic [0:17]  op_tw,
  input  logic [0:17]  op_r_ac,
  input  logic [0:17]  op_r_io,
  input  logic [0:5]   op_r_pf,
  input  logic [0:5]   r_pf_mask
);
  import pdp1_opr_decoder_sva_common::*;

  event comb_ev;
  always @(op_i or op_mask or op_ac or op_io or op_pf or op_tw) -> comb_ev;

  function automatic logic [0:17] exp_ac_base(input logic [0:11] m, input logic [0:17] a, t, input logic [0:5] p);
    return trim18(f_ac_19(m,a,t,p));
  endfunction
  function automatic logic [0:17] exp_io_base(input logic [0:11] m, input logic [0:17] i, input logic oi);
    return trim18(f_io_d_19(m,i,oi));
  endfunction
  function automatic logic [0:5] exp_pf(input logic [0:11] m, input logic [0:5] pf_in, input logic [0:5] pfmsk);
    if (|m[8:11]) begin
      exp_pf = m[8] ? (pf_in | pfmsk) : (pf_in & ~pfmsk);
    end else begin
      exp_pf = pf_in;
    end
  endfunction

  // No-X on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({op_mask,op_ac,op_io,op_pf,op_tw,op_i}))
    |-> !$isunknown({op_r_ac,op_r_io,op_r_pf});

  // Decode r_pf_mask and PF result
  assert property (@(comb_ev) r_pf_mask === f_pf_mask(op_mask[9:11]));
  assert property (@(comb_ev) op_r_pf === exp_pf(op_mask, op_pf, r_pf_mask));

  // PDP-1D AC/IO selection and IO invert-by-op_i
  // ac_path = base AC transform; io_path = base IO path with optional invert by op_i
  logic [0:17] ac_path, io_path;
  always @* begin
    ac_path = exp_ac_base(op_mask, op_ac, op_tw, op_pf);
    io_path = exp_io_base(op_mask, op_io, op_i);
  end

  assert property (@(comb_ev) op_r_ac === (op_mask[6] ? io_path : ac_path));
  assert property (@(comb_ev) op_r_io === (op_mask[7] ? ac_path : io_path));

  // Coverage of D-specific features
  cover property (@(comb_ev) op_mask[6]);     // AC<-IO path select
  cover property (@(comb_ev) op_mask[7]);     // IO<-AC path select
  cover property (@(comb_ev) op_i);           // IO invert engaged
  cover property (@(comb_ev) op_mask[6] && !op_mask[7]);
  cover property (@(comb_ev) !op_mask[6] && op_mask[7]);
  cover property (@(comb_ev) op_mask[6] && op_mask[7]);
endmodule