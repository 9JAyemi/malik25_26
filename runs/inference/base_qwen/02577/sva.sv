module mux_4_to_1_sva (
  input logic sel1,
  input logic sel2,
  input logic [3:0] d0,
  input logic [3:0] d1,
  input logic [3:0] d2,
  input logic [3:0] d3,
  output logic [3:0] out
);
  
  // Mux output should be one of the input signals based on the selection
  mux_output: assert property (
    @(posedge clk) disable iff (!resetn) out == (sel1 & sel2) ? d3 : 
                                              (sel1 & ~sel2) ? d2 : 
                                              (~sel1 & sel2) ? d1 : 
                                              d0
  );
  
endmodule