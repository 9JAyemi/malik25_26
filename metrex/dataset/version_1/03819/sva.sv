// SVA for rotator_byte_reorder
// Bind module + properties (concise but complete)
module rotator_byte_reorder_sva
(
  input logic              clk,
  input logic              load,
  input logic [1:0]        ena,
  input logic [99:0]       data,
  input logic [31:0]       in,
  input logic [31:0]       out,
  input logic [99:0]       rot_data,
  input logic [7:0]        shift_reg0,
  input logic [7:0]        shift_reg1,
  input logic [7:0]        shift_reg2,
  input logic [7:0]        shift_reg3
);

  default clocking cb @(posedge clk); endclocking

  // Track post-initialization (after first load)
  logic initd;
  always_ff @(posedge clk) initd <= initd || load;

  // Load has highest priority
  ap_load_rot:   assert property (load |-> rot_data == data);
  ap_load_shift: assert property (load |-> (shift_reg0 == in[7:0]  &&
                                           shift_reg1 == in[15:8] &&
                                           shift_reg2 == in[23:16] &&
                                           shift_reg3 == in[31:24]));

  // Rotator behavior
  ap_left:  assert property (initd && !load &&  ena[0] && !ena[1]
                             |-> rot_data == {$past(rot_data)[98:0], $past(rot_data)[99]});

  ap_right: assert property (initd && !load && !ena[0] &&  ena[1]
                             |-> rot_data == {$past(rot_data)[0], $past(rot_data)[99:1]});

  // Left has priority over right when both set
  ap_left_prio: assert property (initd && !load && ena[0] && ena[1]
                                 |-> rot_data == {$past(rot_data)[98:0], $past(rot_data)[99]});

  // Hold when no enable
  ap_hold: assert property (initd && !load && (ena == 2'b00)
                            |-> rot_data == $past(rot_data));

  // Byte reordering/shift pipeline (non-load path)
  ap_shift: assert property (initd && !load
                             |-> (shift_reg0 == $past(shift_reg1) &&
                                  shift_reg1 == $past(shift_reg2) &&
                                  shift_reg2 == $past(shift_reg3) &&
                                  shift_reg3 == in[31:24]));

  // Output is OR of byte-concat and lower rot_data
  ap_out: assert property (initd
                           |-> out == ({shift_reg3,shift_reg2,shift_reg1,shift_reg0} | rot_data[31:0]));

  // ---------------------------------
  // Coverage
  // ---------------------------------
  // See both rotation directions
  cp_left:  cover property (initd && !load &&  ena[0] && !ena[1]);
  cp_right: cover property (initd && !load && !ena[0] &&  ena[1]);

  // Priority case (both enables -> left)
  cp_both_left: cover property (initd && !load && (ena == 2'b11));

  // Single-step wrap checks
  cp_wrap_L: cover property (initd && $past(!load && ena[0] && !ena[1])
                             && (rot_data[0] == $past(rot_data[99])));
  cp_wrap_R: cover property (initd && $past(!load && !ena[0] && ena[1])
                             && (rot_data[99] == $past(rot_data[0])));

  // 100-step full cycle (left then return)
  cp_full_cycle_L: cover property (initd ##1 (!load && (ena==2'b01))[*100]
                                   ##1 (rot_data == $past(rot_data,101)));

  // Load followed by 3 shifts moves MSB byte down to shift_reg0
  cp_byte_flow: cover property (load ##1 (!load)[*3]
                                ##1 (shift_reg0 == $past(in[31:24],3)));

endmodule

// Bind to DUT (connect internals)
bind rotator_byte_reorder rotator_byte_reorder_sva sva (
  .clk        (clk),
  .load       (load),
  .ena        (ena),
  .data       (data),
  .in         (in),
  .out        (out),
  .rot_data   (rot_data),
  .shift_reg0 (shift_reg[0]),
  .shift_reg1 (shift_reg[1]),
  .shift_reg2 (shift_reg[2]),
  .shift_reg3 (shift_reg[3])
);