module d_ff(
  input         clock,
  input         reset,
  input  [10:0] io_in,
  input  [10:0] io_init,
  output [10:0] io_out,
  input         io_enable
);
  wire [10:0] d;
  reg [10:0] ff;
  wire  _T_13;
  wire [10:0] _GEN_1;
  assign io_out = ff;
  assign d = _GEN_1;
  assign _T_13 = io_enable == 1'h0;
  assign _GEN_1 = _T_13 ? ff : io_in;
  
  always @(posedge clock) begin
    if (reset) begin
      ff <= io_init;
    end else if (io_enable) begin
      ff <= d;
    end
  end
endmodule