// SVA for initial_config
// Bindable checker focusing on reset, counter behavior, saturation, and start pulse

module initial_config_sva #(
  parameter int REG_SIZE = 20,
  parameter logic [REG_SIZE-1:0] MAX  = 20'hfffff,
  parameter logic [REG_SIZE-1:0] LAST = 20'hffffe
)(
  input logic                  iCLK,
  input logic                  iRST_n,
  input logic                  iINITIAL_ENABLE,
  input logic                  oINITIAL_START,
  input logic [REG_SIZE-1:0]   cnt
);

  default clocking cb @(posedge iCLK); endclocking

  // Asynchronous active-low reset holds cnt at 0
  a_reset_clears:        assert property (!iRST_n |-> cnt == '0);

  // First cycle after reset release increments from 0 to 1
  a_release_increments:  assert property ($rose(iRST_n) |-> cnt == 'd1);

  // While not at MAX, counter increments by 1 each cycle
  a_inc_by_one:          assert property (disable iff (!iRST_n)
                                          (cnt != MAX) |=> (cnt == $past(cnt) + 1));

  // Once at MAX, counter saturates and holds
  a_saturate_hold:       assert property (disable iff (!iRST_n)
                                          (cnt == MAX) |=> (cnt == MAX));

  // Counter never exceeds MAX
  a_no_overflow:         assert property (cnt <= MAX);

  // Start pulse is asserted iff cnt == LAST and enable is high
  a_start_equiv:         assert property (oINITIAL_START == ((cnt == LAST) && iINITIAL_ENABLE));

  // Start pulse is single-cycle
  a_start_one_cycle:     assert property (disable iff (!iRST_n)
                                          oINITIAL_START |=> !oINITIAL_START);

  // Coverage
  c_reach_last:          cover property (disable iff (!iRST_n) (cnt == LAST));
  c_pulse_seen:          cover property (disable iff (!iRST_n) (cnt == LAST && iINITIAL_ENABLE && oINITIAL_START));
  c_saturation_hold:     cover property (disable iff (!iRST_n) (cnt == MAX ##1 cnt == MAX ##1 cnt == MAX));

endmodule

// Bind to DUT
bind initial_config initial_config_sva #(.REG_SIZE(`REG_SIZE)) u_initial_config_sva (
  .iCLK(iCLK),
  .iRST_n(iRST_n),
  .iINITIAL_ENABLE(iINITIAL_ENABLE),
  .oINITIAL_START(oINITIAL_START),
  .cnt(cnt)
);