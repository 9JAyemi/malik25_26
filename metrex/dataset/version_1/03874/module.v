


module mig_7series_v4_0_axi_mc_wr_cmd_fsm #(
parameter integer C_MC_BURST_LEN              = 1,
                     parameter integer C_MC_RD_INST              = 0
  
)
(
input  wire                                 clk           , 
  input  wire                                 reset         , 
  output reg                                  axready       , 
  input  wire                                 axvalid       , 
  output wire                                 cmd_en        , 
  input  wire                                 cmd_full      , 
  output wire                                 next          , 
  input  wire                                 next_pending  ,
  input  wire                                 data_rdy    ,
  output wire                                 b_push        ,
  input  wire                                 b_full        ,
  output wire                                 cmd_en_last   
);

assign cmd_en = (~b_full & axvalid & data_rdy);

    assign next = (~cmd_full & cmd_en);

    assign cmd_en_last = next & ~next_pending;

    assign b_push  = cmd_en_last;

  always @(posedge clk) begin
    if (reset)
      axready <= 1'b0;
    else
      axready <= ~axvalid | cmd_en_last;
  end

endmodule

