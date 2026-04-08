module mem_soft_ecc
  #(
    parameter C_DATA_WIDTH          = 32,
    parameter C_ADDRB_WIDTH         = 10,
    parameter C_HAS_SOFTECC_OUTPUT_REGS_B= 1,
    parameter C_USE_SOFTECC         = 0,
    parameter FLOP_DELAY            = 100
  )
  (
   input                         CLK,
   input      [C_DATA_WIDTH-1:0] DIN,
   output reg [C_DATA_WIDTH-1:0] DOUT,
   input                         SBITERR_IN,
   input                         DBITERR_IN,
   output reg                    SBITERR,
   output reg                    DBITERR,
   input      [C_ADDRB_WIDTH-1:0] RDADDRECC_IN,
   output reg [C_ADDRB_WIDTH-1:0] RDADDRECC
);

  //******************************
  // Port and Generic Definitions
  //******************************
  // C_DATA_WIDTH                  : Memory write/read width
  // C_ADDRB_WIDTH                 : Width of the ADDRB input port
  // C_HAS_SOFTECC_OUTPUT_REGS_B   : Designates the use of a register at the output 
  //                                 of the RAM primitive
  // C_USE_SOFTECC                 : Determines if the Soft ECC feature is used or
  //                                 not. Only applicable Spartan-6
  // FLOP_DELAY                    : Constant delay for register assignments
  //////////////////////////////////////////////////////////////////////////
  // Port Definitions
  //////////////////////////////////////////////////////////////////////////
  // CLK    : Clock to synchronize all read and write operations
  // DIN    : Data input to the Output stage.
  // DOUT   : Final Data output
  // SBITERR_IN    : SBITERR input signal to the Output stage.
  // SBITERR       : Final SBITERR Output signal.
  // DBITERR_IN    : DBITERR input signal to the Output stage.
  // DBITERR       : Final DBITERR Output signal.
  // RDADDRECC_IN  : RDADDRECC input signal to the Output stage.
  // RDADDRECC     : Final RDADDRECC Output signal.
  //////////////////////////////////////////////////////////////////////////

  reg [C_DATA_WIDTH-1:0] dout_i = 0;
  reg sbiterr_i = 0;
  reg dbiterr_i = 0;
  reg [C_ADDRB_WIDTH-1:0] rdaddrecc_i = 0;

  //***********************************************
  // NO OUTPUT REGISTERS.
  //***********************************************
  generate if (C_HAS_SOFTECC_OUTPUT_REGS_B==0) begin : no_output_stage
    always @* begin
      DOUT = DIN;
      RDADDRECC = RDADDRECC_IN;
      SBITERR = SBITERR_IN;
      DBITERR = DBITERR_IN;
    end
  end
  endgenerate

  //***********************************************
  // WITH OUTPUT REGISTERS.
  //***********************************************
  generate if (C_HAS_SOFTECC_OUTPUT_REGS_B==1) begin : has_output_stage
      always @(posedge CLK) begin
      dout_i <= #FLOP_DELAY DIN;
      rdaddrecc_i <= #FLOP_DELAY RDADDRECC_IN;
      sbiterr_i <= #FLOP_DELAY SBITERR_IN;
      dbiterr_i <= #FLOP_DELAY DBITERR_IN;
      end

      always @* begin
      DOUT = dout_i;
      RDADDRECC = rdaddrecc_i;
      SBITERR = sbiterr_i;
      DBITERR = dbiterr_i;
      end //end always
  end //end in_or_out_stage generate statement
  endgenerate

endmodule