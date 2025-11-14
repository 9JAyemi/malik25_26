// SVA for the given design. Bind these to the DUTs.
// Uses only @(*) (combinational) sampling; no testbench/clock required.

// Barrel shifter: functional correctness, internal wiring, and branch coverage
module barrel_shifter_sva(
  input  logic [7:0] in,
  input  logic [2:0] shift,
  input  logic [7:0] out,
  input  logic [7:0] shifted
);
  let exp_bs =
      shift[2] ? 8'h00 :
      shift[1] ? {in[0],    in[7:1]} :
      shift[0] ? {in[1:0],  in[7:2]} :
                 {in[2:0],  in[7:3]};

  // Out equals internal wire and expected value
  assert property (@(*)) out == shifted;
  assert property (@(*)) shifted == exp_bs;
  assert property (@(*)) out     == exp_bs;

  // Branch coverage of the priority chain
  cover property (@(*)) shift[2];
  cover property (@(*)) !shift[2] && shift[1];
  cover property (@(*)) !shift[2] && !shift[1] && shift[0];
  cover property (@(*)) !shift[2] && !shift[1] && !shift[0];
endmodule

bind barrel_shifter barrel_shifter_sva bs_sva (.*);


// Binary tree adder: parity structure and zero-extended output
module binary_tree_adder_sva(
  input  logic [7:0] in,
  input  logic [7:0] out,
  input  logic [7:0] sum
);
  // Expected 1-bit parities
  let p0 = in[0];
  let p1 = ^in[1:0];
  let p2 = ^in[3:2];
  let p3 = ^in[3:0];
  let p4 = ^in[5:4];
  let p5 = ^in[7:4];
  let p6 = ^in;

  // Internal nodes check the intended parity tree
  assert property (@(*))
    (sum[0] == p0) && (sum[1] == p1) && (sum[2] == p2) &&
    (sum[3] == p3) && (sum[4] == p4) && (sum[5] == p5) &&
    (sum[6] == p6);

  // Output is zero-extended parity
  assert property (@(*)) out == {7'b0, sum[6]};
  assert property (@(*)) out[7:1] == '0;

  // Cover both parity outcomes
  cover property (@(*)) (^in);
  cover property (@(*)) (!^in);
endmodule

bind binary_tree_adder binary_tree_adder_sva bta_sva (.*);


// Addictive control logic: correct mode selection and end-to-end function
module addictive_control_logic_sva(
  input  logic [7:0] in,
  input  logic       select,
  input  logic [7:0] out
);
  let rot3 = {in[2:0], in[7:3]};
  let par8 = ^in;

  // Mode checks
  assert property (@(*)) (!select) |-> (out == rot3);
  assert property (@(*)) ( select) |-> (out == {7'b0, par8});

  // Cover both modes
  cover property (@(*)) select == 0;
  cover property (@(*)) select == 1;
endmodule

bind addictive_control_logic addictive_control_logic_sva acl_sva (.*);


// Top-level: redundancy check of overall behavior
module top_module_sva(
  input  logic [7:0] in,
  input  logic       select,
  input  logic [7:0] out
);
  let rot3 = {in[2:0], in[7:3]};
  let par8 = ^in;

  assert property (@(*)) out ==
    (select ? {7'b0, par8} : rot3);

  cover property (@(*)) (select == 0) && (out == rot3);
  cover property (@(*)) (select == 1) && (out == {7'b0, par8});
endmodule

bind top_module top_module_sva top_sva (.*);