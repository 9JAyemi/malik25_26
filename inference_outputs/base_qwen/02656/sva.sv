```systemverilog
module wireless_communication_block_sva (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  input logic [1:0] ctrl,
  output logic [7:0] data_out
);

  // Sequential logic to ensure data_out is assigned correctly based on ctrl
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'b00000000;
    end else begin
      data_out <= (ctrl == 2'b00) ? data_in :
                  (ctrl == 2'b01) ? data_in :
                  (ctrl == 2'b10) ? data_in :
                  8'b00000000;
    end
  end

  // Combinational logic to ensure data_out is assigned correctly based on ctrl
  // This is redundant with the sequential logic but included for completeness
  always_comb begin
    data_out = (ctrl == 2'b00) ? data_in :
               (ctrl == 2'b01) ? data_in :
               (ctrl == 2'b10) ? data_in :
               8'b00000000;
  end

  // Property to check that data_out is assigned correctly based on ctrl
  property p_data_out_assignment;
    @(posedge clk) disable iff (!rst_n) data_out == (ctrl == 2'b00) ? data_in :
                                                       (ctrl == 2'b01) ? data_in :
                                                       (ctrl == 2'b10) ? data_in :
                                                       8'b00000000;
  endproperty

  // Assert the property
  a_data_out_assignment: assert property (p_data_out_assignment)
    else $error("data_out assignment is incorrect");

  // Property to check that data_out is not assigned when ctrl is invalid
  property p_data_out_invalid_ctrl;
    @(posedge clk) disable iff (!rst_n) (ctrl != 2'b00 && ctrl != 2'b01 && ctrl != 2'b10) |-> data_out == 8'b00000000;
  endproperty

  // Assert the property
  a_data_out_invalid_ctrl: assert property (p_data_out_invalid_ctrl)
    else $error("data_out assigned when ctrl is invalid");

endmodule
```