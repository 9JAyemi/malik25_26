module mux_4_to_1 (
  input sel1,
  input sel2,
  input [3:0] d0,
  input [3:0] d1,
  input [3:0] d2,
  input [3:0] d3,
  output [3:0] out
);
  
  assign out = (sel1 & sel2) ? d3 : 
               (sel1 & ~sel2) ? d2 : 
               (~sel1 & sel2) ? d1 : 
               d0;
  
endmodule
