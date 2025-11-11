
module UpDownCtr(
  input        clock,
  input        reset,
  input  [9:0] io_strideInc,
  input  [9:0] io_strideDec,
  input        io_inc,
  input        io_dec,
  output [9:0] io_out,
  output [9:0] io_nextInc,
  output [9:0] io_nextDec
);
  reg  [9:0] reg$;  
  wire [9:0] reg$_T_1;
  wire [9:0] reg$_T_2;
  wire [9:0] reg$_T_3;

  assign io_out = reg$;
  assign io_nextInc = reg$ + io_strideInc;
  assign io_nextDec = reg$ - io_strideDec;
  assign reg$_T_1 = io_inc ? io_strideInc : 10'h0;
  assign reg$_T_2 = io_dec ? io_strideDec : 10'h0;

  always @(posedge clock) begin
    if (reset) begin
      reg$ <= 10'h0;
    end else begin
      reg$ <= reg$_T_3;
    end
  end

  assign reg$_T_3 = io_inc | io_dec ? reg$ + reg$_T_1 - reg$_T_2 : reg$;

endmodule