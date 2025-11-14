
module bsg_channel_narrow #( parameter width_in_p     = 8
                           , parameter width_out_p    = 4
                           , parameter lsb_to_msb_p  = 1
                           )
                          ( input                    clk_i
                          , input                    reset_i
                          , input  [width_in_p-1:0]  data_i
                          , input                    deque_i
                          , output [width_out_p-1:0] data_o
                          , output                   deque_o
                          );
  // Internal signals
  reg [width_out_p-1:0] narrowed_data;

  // Narrowing the input data
  always @(posedge clk_i or posedge reset_i)
    if(reset_i)
      narrowed_data <= {width_out_p{1'b0}};
    else
      narrowed_data <= (lsb_to_msb_p) ? data_i[width_out_p-1:0] : data_i[width_in_p-1:width_in_p-width_out_p];

  // Output signals
  assign data_o = narrowed_data;
  assign deque_o = deque_i;

endmodule