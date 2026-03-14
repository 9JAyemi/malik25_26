module synch_3 #(parameter WIDTH = 1) (
   input  wire [WIDTH-1:0] i,     // input signal
   output reg  [WIDTH-1:0] o,     // synchronized output
   input  wire             clk    // clock to synchronize on
);

reg [WIDTH-1:0] stage_1;
reg [WIDTH-1:0] stage_2;
reg [WIDTH-1:0] stage_3;

always @(posedge clk) begin
   stage_1 <= i;
   stage_2 <= stage_1;
   stage_3 <= stage_2;
   o <= stage_3;
end

endmodule