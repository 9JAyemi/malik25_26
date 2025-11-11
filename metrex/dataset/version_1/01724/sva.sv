// SVA checker for priority_encoder. Bind this to the DUT and drive clk from TB.
module priority_encoder_sva (
  input logic                   clk,
  input logic [15:0]            data_in,
  input logic [1:0]             priority_input,
  input logic [1:0]             highest_input
);

  default clocking cb @(posedge clk); endclocking

  // Priority encoding correctness
  ap_prio_15:      assert property (data_in[15]                  |-> priority_input == 2'b01);
  ap_prio_14only:  assert property (!data_in[15] &&  data_in[14] |-> priority_input == 2'b10);
  ap_prio_none:    assert property (!data_in[15] && !data_in[14] |-> priority_input == 2'b00);
  ap_prio_no11:    assert property (priority_input inside {2'b00,2'b01,2'b10});

  // Highest-input mapping (compact equivalence)
  ap_high_eq: assert property (
    (priority_input inside {2'b00,2'b01,2'b10})
    |-> highest_input == (
          (priority_input +
           ((priority_input==2'b00) ? data_in[0] :
            (priority_input==2'b01) ? data_in[1] :
                                       data_in[2]))[1:0]
        )
  );

  // Knownness/X checks (only when relevant inputs are known)
  ap_no_x_prio: assert property (!$isunknown({data_in[15],data_in[14]}) |-> !$isunknown(priority_input));
  ap_no_x_high: assert property (
    ((priority_input==2'b00 && !$isunknown(data_in[0])) ||
     (priority_input==2'b01 && !$isunknown(data_in[1])) ||
     (priority_input==2'b10 && !$isunknown(data_in[2])))
    |-> !$isunknown(highest_input)
  );

  // Functional coverage
  cp_prio_00: cover property (!data_in[15] && !data_in[14] && priority_input==2'b00);
  cp_prio_01: cover property ( data_in[15]                   && priority_input==2'b01);
  cp_prio_10: cover property (!data_in[15] &&  data_in[14]   && priority_input==2'b10);
  cp_15_overrides_14: cover property (data_in[15] && data_in[14] && priority_input==2'b01);

  cp_h_00_0: cover property (priority_input==2'b00 && !data_in[0] && highest_input==2'b00);
  cp_h_00_1: cover property (priority_input==2'b00 &&  data_in[0] && highest_input==2'b01);
  cp_h_01_0: cover property (priority_input==2'b01 && !data_in[1] && highest_input==2'b01);
  cp_h_01_1: cover property (priority_input==2'b01 &&  data_in[1] && highest_input==2'b10);
  cp_h_10_0: cover property (priority_input==2'b10 && !data_in[2] && highest_input==2'b10);
  cp_h_10_1: cover property (priority_input==2'b10 &&  data_in[2] && highest_input==2'b11);

endmodule

// Example bind (provide a clock from your TB):
// bind priority_encoder priority_encoder_sva u_sva(.clk(tb_clk), .data_in(data_in), .priority_input(priority_input), .highest_input(highest_input));