`ifdef INCL_CDC_3FF
`else
`define INCL_CDC_3FF

module cdc_3ff #(
  parameter DATA_WIDTH = 1,
  parameter INIT_VALUE = 0
) (
  input      target_clk,
  input      reset,

  input      [DATA_WIDTH-1:0] input_signal,
  output reg [DATA_WIDTH-1:0] output_signal
);

 reg [DATA_WIDTH-1:0] signal_meta  ;
 reg [DATA_WIDTH-1:0] signal_d  ;

always @ (posedge target_clk or posedge reset) begin
  if (reset) begin
    signal_meta   <= INIT_VALUE;
    signal_d      <= INIT_VALUE;
    output_signal <= INIT_VALUE;
  end else begin
    signal_meta   <= input_signal;
    signal_d      <= signal_meta;
    output_signal <= signal_d;
  end
end

endmodule

`endif 