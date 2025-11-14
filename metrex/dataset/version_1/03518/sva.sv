// SVA for antares_shifter
// Bind this module to the DUT; provide a sampling clock and reset.
// Functional spec assumed:
//  - direction=1'b1: logical left shift (zero-fill), sign_extend ignored
//  - direction=1'b0: right shift; sign_extend=0 => logical, =1 => arithmetic

module antares_shifter_sva (
  input logic                clk,
  input logic                rst_n,
  input logic [31:0]         shift_input_data,
  input logic [4:0]          shift_shamnt,
  input logic                shift_direction,
  input logic                shift_sign_extend,
  input logic [31:0]         shift_result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Reference model
  function automatic [31:0] ref_shift (
    input logic [31:0] din,
    input logic [4:0]  shamt,
    input logic        dir,
    input logic        sext
  );
    if (dir)        ref_shift = din << shamt;                   // left logical
    else if (sext)  ref_shift = $signed(din) >>> shamt;         // right arithmetic
    else            ref_shift = din >> shamt;                   // right logical
  endfunction

  function automatic bit no_x32(input logic [31:0] v); no_x32 = !$isunknown(v); endfunction

  // Core functional equivalence
  assert property (1'b1 |-> shift_result == ref_shift(shift_input_data, shift_shamnt, shift_direction, shift_sign_extend))
    else $error("antares_shifter: functional mismatch");

  // Identity shift when shamt==0
  assert property (shift_shamnt == 5'd0 |-> shift_result == shift_input_data)
    else $error("antares_shifter: shamt=0 not identity");

  // Left shift must zero-fill lower shamt bits
  assert property ((shift_direction && (shift_shamnt != 0)) |-> shift_result[0 +: shift_shamnt] == '0)
    else $error("antares_shifter: left shift tail not zero");

  // Right logical must zero-fill upper shamt bits
  assert property ((!shift_direction && !shift_sign_extend && (shift_shamnt != 0)) |-> shift_result[31 -: shift_shamnt] == '0)
    else $error("antares_shifter: srl head not zero");

  // Right arithmetic must sign-fill upper shamt bits
  assert property ((!shift_direction && shift_sign_extend && (shift_shamnt != 0)) |-> shift_result[31 -: shift_shamnt] == {shift_shamnt{shift_input_data[31]}})
    else $error("antares_shifter: sra head not sign-filled");

  // No-X propagation when inputs are known
  assert property ( no_x32(shift_input_data) && !$isunknown(shift_shamnt) &&
                    !$isunknown(shift_direction) && !$isunknown(shift_sign_extend)
                    |-> no_x32(shift_result))
    else $error("antares_shifter: X in result with known inputs");

  // -------- Coverage (concise but meaningful) --------
  // Exercise modes and extremes
  cover property (shift_direction && (shift_shamnt == 5'd0));     // SLL by 0
  cover property (shift_direction && (shift_shamnt == 5'd31));    // SLL by 31
  cover property (!shift_direction && !shift_sign_extend && (shift_shamnt == 5'd31)); // SRL by 31
  cover property (!shift_direction && shift_sign_extend &&  shift_input_data[31] && (shift_shamnt == 5'd1));  // SRA, MSB=1
  cover property (!shift_direction && shift_sign_extend && !shift_input_data[31] && (shift_shamnt == 5'd1));  // SRA, MSB=0

  // Exercise shamt activity in each mode
  cover property ($changed(shift_shamnt) &&  shift_direction);                // SLL varying shamt
  cover property ($changed(shift_shamnt) && !shift_direction &&  shift_sign_extend);  // SRA varying shamt
  cover property ($changed(shift_shamnt) && !shift_direction && !shift_sign_extend);  // SRL varying shamt

  // Toggle controls
  cover property ($changed(shift_direction));
  cover property ($changed(shift_sign_extend));

endmodule

// Example bind (edit clk/rst signals to your environment):
// bind antares_shifter antares_shifter_sva u_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .shift_input_data(shift_input_data), .shift_shamnt(shift_shamnt),
//   .shift_direction(shift_direction), .shift_sign_extend(shift_sign_extend),
//   .shift_result(shift_result) );