module mux4 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, d2, d3, 
              input  [1:0] sel, 
              output [WIDTH-1:0] y);

  wire [WIDTH-1:0] s0, s1;
  assign s0 = sel[0] ? d2 : d0;
  assign s1 = sel[0] ? d3 : d1;
  assign y = sel[1] ? s1 : s0;

endmodule