// SVA for acl_vector_to_stream_converter_single
// Bind this checker to the DUT. Concise checks of handshakes, staging, CDC gating,
// stability under stall, start/flush behavior, and basic coverage.

module acl_vector_to_stream_converter_single_sva #(parameter WIDTH=32) (
  input  logic                  clock,
  input  logic                  clock2x,
  input  logic                  resetn,
  input  logic                  start,
  input  logic                  valid_in,
  input  logic                  stall_in,
  input  logic [WIDTH-1:0]      a1,
  input  logic [WIDTH-1:0]      a2,
  input  logic [WIDTH-1:0]      dataa,
  input  logic                  valid_out,
  input  logic                  stall_out,

  // internal
  input  logic [WIDTH-1:0]      a1_sr,
  input  logic [WIDTH-1:0]      a2_sr,
  input  logic                  sr_in_valid,
  input  logic                  stall_sr,
  input  logic                  start_reg,

  input  logic                  sel2x,
  input  logic                  sel_ref,
  input  logic                  w,

  input  logic [WIDTH-1:0]      a1_reg,
  input  logic [WIDTH-1:0]      a2_reg,
  input  logic                  valid_reg,
  input  logic                  stall_reg,

  input  logic [WIDTH-1:0]      shift_reg_a1,
  input  logic [WIDTH-1:0]      shift_reg_a2,
  input  logic                  valid_a1,
  input  logic                  valid_a2,
  input  logic                  start_reg_2x,
  input  logic                  read_data,
  input  logic                  stall_shift
);

  // Clocking
  default clocking cb_clk @(posedge clock); endclocking
  clocking cb_clk2x @(posedge clock2x); endclocking

  // Reset clears
  assert property (@cb_clk !resetn |-> (!sr_in_valid && !valid_reg && !stall_out));
  assert property (@cb_clk2x !resetn |-> (!valid_out && !valid_a1 && !valid_a2 && !read_data));

  // Combinational ties
  assert property (@cb_clk   stall_out == sr_in_valid);
  assert property (@cb_clk   stall_sr  == (valid_reg & stall_reg));
  assert property (@cb_clk2x valid_out == valid_a1);
  assert property (@cb_clk2x dataa     == shift_reg_a1);
  assert property (@cb_clk2x stall_shift == stall_in);
  assert property (@cb_clk2x stall_reg == ~read_data);
  assert property (@cb_clk2x w == (sel_ref == sel2x));

  // 2x clock toggling check
  assert property (@cb_clk2x disable iff (!resetn) sel2x != $past(sel2x));

  // Upstream reg stage: stability under stall
  assert property (@cb_clk disable iff (!resetn)
    (valid_reg && stall_reg) |=> (valid_reg && $stable(a1_reg) && $stable(a2_reg)));

  // Start behavior
  assert property (@cb_clk disable iff (!resetn) start |=> !valid_reg);
  // Flush eventually reaches output (bounded)
  assert property (@cb_clk disable iff (!resetn) start |-> ##[1:4] !valid_out);

  // SR stage: capture/hold/clear
  assert property (@cb_clk disable iff (!resetn)
    (!sr_in_valid && stall_sr && !start)
      |=> (sr_in_valid == $past(valid_in)) && (a1_sr == $past(a1)) && (a2_sr == $past(a2)));
  assert property (@cb_clk disable iff (!resetn)
    (sr_in_valid && stall_sr && !start)
      |=> (sr_in_valid && $stable(a1_sr) && $stable(a2_sr)));
  assert property (@cb_clk disable iff (!resetn)
    (!stall_sr || start) |=> !sr_in_valid);

  // Reg stage load when allowed (and not starting)
  assert property (@cb_clk disable iff (!resetn)
    (!start && (~valid_reg || ~stall_reg))
      |=> (valid_reg == ($past(valid_in) || $past(sr_in_valid))) &&
          (a1_reg == ($past(sr_in_valid) ? $past(a1_sr) : $past(a1))) &&
          (a2_reg == ($past(sr_in_valid) ? $past(a2_sr) : $past(a2))));

  // Read pulse implies source valid was present
  assert property (@cb_clk2x disable iff (!resetn) $rose(read_data) |-> valid_reg);

  // Output stability under backpressure
  assert property (@cb_clk2x disable iff (!resetn)
    (stall_in && valid_out) |=> (valid_out && $stable(dataa)));
  assert property (@cb_clk2x disable iff (!resetn)
    (stall_in && $past(stall_in) && valid_out) |-> ($stable(valid_out) && $stable(dataa)));

  // No X on outputs after reset
  assert property (@cb_clk2x disable iff (!resetn) !$isunknown({valid_out, dataa}));
  assert property (@cb_clk   disable iff (!resetn) !$isunknown(stall_out));

  // Coverage: accept path, stall, and flush
  cover property (@cb_clk2x disable iff (!resetn)
    (valid_out && stall_in)[*2] ##1 (!stall_in) ##1 valid_out);

  cover property (@cb_clk disable iff (!resetn)
    (valid_in && !start)[*2] ##[1:6] valid_out);

  cover property (@cb_clk disable iff (!resetn)
    start ##[1:4] !valid_out ##1 valid_out);

endmodule

bind acl_vector_to_stream_converter_single
  acl_vector_to_stream_converter_single_sva #(.WIDTH(WIDTH)) sva (
    .clock(clock),
    .clock2x(clock2x),
    .resetn(resetn),
    .start(start),
    .valid_in(valid_in),
    .stall_in(stall_in),
    .a1(a1),
    .a2(a2),
    .dataa(dataa),
    .valid_out(valid_out),
    .stall_out(stall_out),

    .a1_sr(a1_sr),
    .a2_sr(a2_sr),
    .sr_in_valid(sr_in_valid),
    .stall_sr(stall_sr),
    .start_reg(start_reg),

    .sel2x(sel2x),
    .sel_ref(sel_ref),
    .w(w),

    .a1_reg(a1_reg),
    .a2_reg(a2_reg),
    .valid_reg(valid_reg),
    .stall_reg(stall_reg),

    .shift_reg_a1(shift_reg_a1),
    .shift_reg_a2(shift_reg_a2),
    .valid_a1(valid_a1),
    .valid_a2(valid_a2),
    .start_reg_2x(start_reg_2x),
    .read_data(read_data),
    .stall_shift(stall_shift)
  );