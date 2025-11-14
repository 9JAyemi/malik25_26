module axis_infrastructure_v1_1_clock_synchronizer # (
  parameter integer C_NUM_STAGES              = 4
)     
(
  input  wire                               clk,
  input  wire                               synch_in ,
  output wire                               synch_out
);

localparam integer P_SYNCH_D_WIDTH = (C_NUM_STAGES > 0) ? C_NUM_STAGES : 1;
 reg [P_SYNCH_D_WIDTH-1:0] synch_d = 'b0;

  generate 
  if (C_NUM_STAGES > 0) begin : gen_synchronizer
    genvar i;

    always @(posedge clk) begin
      synch_d[0] <= synch_in;
    end

    for (i = 1; i < C_NUM_STAGES ; i = i + 1) begin : gen_stage
      always @(posedge clk) begin
        synch_d[i] <= synch_d[i-1];
      end
    end

    assign synch_out = synch_d[C_NUM_STAGES-1];
  end
  else begin : gen_no_synchronizer
    assign synch_out = synch_in;
  end
  endgenerate

endmodule