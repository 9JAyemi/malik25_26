// SVA for Update_Count_From_AB
module Update_Count_From_AB_sva (
  input  logic                      CLK_IN,
  input  logic                      reset,
  input  logic                      enb,
  input  logic                      A,
  input  logic                      B,
  input  logic                      index,
  input  logic signed [15:0]        count_max,
  input  logic signed [15:0]        count,

  input  logic [1:0]                is_libEncoderPeripheralHdl_c7_Update_Count_From_AB,
  input  logic [2:0]                is_INDEX,
  input  logic signed [15:0]        count_reg,

  input  logic [1:0]                is_libEncoderPeripheralHdl_c7_Update_Count_From_AB_next,
  input  logic [2:0]                is_INDEX_next,
  input  logic signed [15:0]        count_reg_next
);

  localparam int IN_NO_ACTIVE_CHILD = 0,
                 IN_A0_B0           = 1,
                 IN_A0_B1           = 2,
                 IN_A1_B0           = 3,
                 IN_A1_B1           = 4;
  localparam int IN_INDEX           = 0,
                 IN_INIT            = 1;

  default clocking cb @(posedge CLK_IN); endclocking

  // Assumptions/encoding sanity
  assume  property (count_max >= 16'sd0);
  assert  property (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB inside {IN_INDEX, IN_INIT});
  assert  property (is_INDEX inside {IN_NO_ACTIVE_CHILD, IN_A0_B0, IN_A0_B1, IN_A1_B0, IN_A1_B1});

  // Reset behavior
  assert property (@(posedge CLK_IN)
                   reset |-> (is_INDEX==IN_NO_ACTIVE_CHILD &&
                              is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INIT &&
                              count_reg==16'sd0));

  // Hold when enb==0
  assert property (disable iff (reset)
                   !enb |=> ($stable(is_INDEX) &&
                             $stable(is_libEncoderPeripheralHdl_c7_Update_Count_From_AB) &&
                             $stable(count_reg)));

  // Registered state/data == combinational next on enb
  assert property (disable iff (reset)
                   enb |=> (is_INDEX == $past(is_INDEX_next) &&
                            is_libEncoderPeripheralHdl_c7_Update_Count_From_AB == $past(is_libEncoderPeripheralHdl_c7_Update_Count_From_AB_next) &&
                            count_reg == $past(count_reg_next)));

  // Count output equals next-value
  assert property (count == count_reg_next);

  // Range constraint while active
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX)
                   |-> (count_reg >= 16'sd0 && count_reg <= count_max));

  // Default transition when not in IN_INDEX
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB!=IN_INDEX)
                   |-> (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB_next==IN_INDEX &&
                        is_INDEX_next==IN_A0_B0 &&
                        count_reg_next==16'sd0));

  // Index pulse clears and aligns
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && index)
                   |-> (count_reg_next==16'sd0 &&
                        is_INDEX_next==IN_A0_B0 &&
                        is_libEncoderPeripheralHdl_c7_Update_Count_From_AB_next==IN_INDEX));

  // Quadrature transitions and count update (with wrap)
  // IN_A0_B0
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B0 &&  A && !B)
                   |-> (is_INDEX_next==IN_A1_B0 &&
                        count_reg_next==((count_reg==count_max)?16'sd0:(count_reg+16'sd1))));
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B0 && !A &&  B)
                   |-> (is_INDEX_next==IN_A0_B1 &&
                        count_reg_next==((count_reg==16'sd0)?count_max:(count_reg-16'sd1))));

  // IN_A0_B1
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B1 &&  A &&  B)
                   |-> (is_INDEX_next==IN_A1_B1 &&
                        count_reg_next==((count_reg==16'sd0)?count_max:(count_reg-16'sd1))));
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B1 && !A && !B)
                   |-> (is_INDEX_next==IN_A0_B0 &&
                        count_reg_next==((count_reg==count_max)?16'sd0:(count_reg+16'sd1))));

  // IN_A1_B0
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A1_B0 && !A && !B)
                   |-> (is_INDEX_next==IN_A0_B0 &&
                        count_reg_next==((count_reg==16'sd0)?count_max:(count_reg-16'sd1))));
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A1_B0 &&  A &&  B)
                   |-> (is_INDEX_next==IN_A1_B1 &&
                        count_reg_next==((count_reg==count_max)?16'sd0:(count_reg+16'sd1))));

  // IN_A1_B1
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A1_B1 && !A &&  B)
                   |-> (is_INDEX_next==IN_A0_B1 &&
                        count_reg_next==((count_reg==count_max)?16'sd0:(count_reg+16'sd1))));
  assert property (disable iff (reset)
                   (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A1_B1 &&  A && !B)
                   |-> (is_INDEX_next==IN_A1_B0 &&
                        count_reg_next==((count_reg==16'sd0)?count_max:(count_reg-16'sd1))));

  // Hold when no valid A/B transition in current substate (index low)
  assert property (disable iff (reset)
    (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && !index &&
     ((is_INDEX==IN_A0_B0 && !(A && !B) && !(!A && B)) ||
      (is_INDEX==IN_A0_B1 && !((A && B) || (!A && !B))) ||
      (is_INDEX==IN_A1_B0 && !((!A && !B) || (A && B))) ||
      (is_INDEX==IN_A1_B1 && !((!A && B) || (A && !B)))))
    |-> (is_INDEX_next==is_INDEX && count_reg_next==count_reg)
  );

  // Coverage
  cover property (disable iff (reset) enb ##1 (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B0));
  cover property (disable iff (reset) (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && index));
  cover property (disable iff (reset) (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B0 && A && !B && count_reg==count_max)); // inc wrap
  cover property (disable iff (reset) (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A0_B1 && A && B && count_reg==16'sd0));     // dec wrap
  cover property (disable iff (reset) (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A1_B0 && A && B));
  cover property (disable iff (reset) (is_libEncoderPeripheralHdl_c7_Update_Count_From_AB==IN_INDEX && is_INDEX==IN_A1_B1 && A && !B));

endmodule

bind Update_Count_From_AB Update_Count_From_AB_sva sva_inst (.*);