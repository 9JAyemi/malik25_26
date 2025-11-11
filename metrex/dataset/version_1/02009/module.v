

module sm_timer_64
(
  output wire             sCMD_tready   ,
  input  wire             sCMD_tvalid   ,
  input  wire  [31 : 0]   sCMD_tdata    ,

  input  wire             mRet_tready   ,
  output wire             mRet_tvalid   ,
  output wire  [31 : 0]   mRet_tdata    ,

  input  wire             ACLK          ,
  input  wire             ARESETN
);

localparam Fetch           = 8'b00000001; localparam Decode          = 8'b00000010; localparam SMSTART         = 8'b00000100; localparam SMRESET         = 8'b00001000; localparam SMSTOP          = 8'b00010000; localparam SMLAP           = 8'b00100000; localparam SMSEND_Lo       = 8'b01000000; localparam SMSEND_Hi       = 8'b10000000; localparam OPSTART         = 16'h1;
localparam OPSTOP          = 16'h2;
localparam OPRESET         = 16'h3;
localparam OPREAD          = 16'h4;
localparam OPLAP           = 16'h5;

reg [ 7:0] state       ;
reg [31:0] instruction ;
reg [31:0] rVal        ;

assign mRet_tdata  = rVal;
assign sCMD_tready = (state == Fetch);
assign mRet_tvalid = (state == SMSEND_Lo || state == SMSEND_Hi);
reg  [63 : 0]  counterR;

reg            rRESET;
reg            rEN;

always @(posedge ACLK) begin
  if (rRESET) begin
    counterR <= 64'd0;
  end
  else begin
    if (rEN) begin
      counterR <= counterR + 1;
    end
  end
end


always @(posedge ACLK)
begin
  if(!ARESETN) begin
    state <= Fetch;
    instruction <= 32'd0;
    rVal  <= 32'd0;
    rEN   <= 1'b0;
    rRESET<= 1'b1;
  end
  else begin
    case (state)

      Fetch: begin
        rRESET <= 1'b0;
        if (sCMD_tvalid == 1) begin
          instruction  <= sCMD_tdata;
          state        <= Decode;
        end
        else begin
          state        <= Fetch;
        end
      end

      Decode: begin
        case (instruction[31:16])
          OPSTART: begin
            rEN <= 1'b1;
            state        <= Fetch;
          end

          OPSTOP: begin
            rEN <= 1'b0;
            state        <= Fetch;
          end

          OPRESET: begin
            rRESET <= 1'b1;
            state        <= Fetch;
          end

          OPREAD: begin
            rVal         <= counterR[31:0];
            state        <= SMSEND_Lo;
          end

          default: begin
            state        <= Fetch;
          end
        endcase
      end

      SMSEND_Lo: begin
        if (mRet_tready == 1) begin
          rVal  <= counterR[63:32];
          state <= SMSEND_Hi;
        end
        else begin
          state <= SMSEND_Lo;
        end
      end

      SMSEND_Hi: begin
        if (mRet_tready == 1) begin
          state <= Fetch;
        end
        else begin
          state <= SMSEND_Hi;
        end
      end

    endcase
  end
end

endmodule


