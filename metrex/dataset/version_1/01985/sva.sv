// SVA for my_fir_h3
// Bind this checker to the DUT; concise but covers shift, hold, ready, and MAC correctness.

module my_fir_h3_sva #(
  parameter int WIDTH   = 5'b10000,
  parameter int COEF0_3 = -9,
  parameter int COEF1_3 = -56,
  parameter int COEF2_3 = -109,
  parameter int COEF4_3 = 109,
  parameter int COEF5_3 = 56,
  parameter int COEF6_3 = 9
)(
  input  logic                 clk,
  input  logic                 new_data_rdy,
  input  logic                 output_data_ready,
  input  logic [WIDTH-1:0]     din,
  input  logic [28-1:0]        dout,
  input  logic [WIDTH-1:0]     n_delay_reg1,
  input  logic [WIDTH-1:0]     n_delay_reg2,
  input  logic [WIDTH-1:0]     n_delay_reg3,
  input  logic [WIDTH-1:0]     n_delay_reg4,
  input  logic [WIDTH-1:0]     n_delay_reg5,
  input  logic [WIDTH-1:0]     n_delay_reg6
);

  // past-valid guard (no reset in DUT)
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // expected MAC (truncated to 28 bits like DUT)
  function automatic signed [27:0] mac_exp(
    input logic [WIDTH-1:0] din_i,
    input logic [WIDTH-1:0] r1, r2, r4, r5, r6
  );
    mac_exp = $signed(din_i)*COEF0_3
            + $signed(r1)  *COEF1_3
            + $signed(r2)  *COEF2_3
            + $signed(r4)  *COEF4_3
            + $signed(r5)  *COEF5_3
            + $signed(r6)  *COEF6_3;
  endfunction

  // Ready mirrors request
  assert property (@(posedge clk)
    output_data_ready == new_data_rdy
  );

  // Hold all state and output when idle
  assert property (@(posedge clk) disable iff(!past_valid)
    !new_data_rdy |-> $stable({n_delay_reg1,n_delay_reg2,n_delay_reg3,
                               n_delay_reg4,n_delay_reg5,n_delay_reg6,dout})
  );

  // Shift-register updates on valid
  assert property (@(posedge clk) disable iff(!past_valid)
    new_data_rdy |-> ( n_delay_reg1 ==          din
                    && n_delay_reg2 == $past(n_delay_reg1)
                    && n_delay_reg3 == $past(n_delay_reg2)
                    && n_delay_reg4 == $past(n_delay_reg3)
                    && n_delay_reg5 == $past(n_delay_reg4)
                    && n_delay_reg6 == $past(n_delay_reg5) )
  );

  // Output MAC correctness on valid
  assert property (@(posedge clk) disable iff(!past_valid)
    new_data_rdy |-> dout == mac_exp(din,
                                     $past(n_delay_reg1),
                                     $past(n_delay_reg2),
                                     $past(n_delay_reg4),
                                     $past(n_delay_reg5),
                                     $past(n_delay_reg6))
  );

  // Optional stronger pipeline check across 6 consecutive valids
  assert property (@(posedge clk) disable iff(!past_valid)
    new_data_rdy && $past(new_data_rdy,1) && $past(new_data_rdy,2)
    && $past(new_data_rdy,3) && $past(new_data_rdy,4) && $past(new_data_rdy,5)
    |-> n_delay_reg6 == $past(din,5)
  );

  // Functional coverage
  cover property (@(posedge clk) new_data_rdy);                  // at least one valid
  cover property (@(posedge clk) new_data_rdy ##1 new_data_rdy); // back-to-back valid
  cover property (@(posedge clk) !new_data_rdy [*3]);            // idle stretch
  cover property (@(posedge clk) new_data_rdy [*6]);             // long valid burst

endmodule

// Bind to DUT
bind my_fir_h3 my_fir_h3_sva #(
  .WIDTH(WIDTH),
  .COEF0_3(COEF0_3),
  .COEF1_3(COEF1_3),
  .COEF2_3(COEF2_3),
  .COEF4_3(COEF4_3),
  .COEF5_3(COEF5_3),
  .COEF6_3(COEF6_3)
) my_fir_h3_sva_i (
  .clk(clk),
  .new_data_rdy(new_data_rdy),
  .output_data_ready(output_data_ready),
  .din(din),
  .dout(dout),
  .n_delay_reg1(n_delay_reg1),
  .n_delay_reg2(n_delay_reg2),
  .n_delay_reg3(n_delay_reg3),
  .n_delay_reg4(n_delay_reg4),
  .n_delay_reg5(n_delay_reg5),
  .n_delay_reg6(n_delay_reg6)
);