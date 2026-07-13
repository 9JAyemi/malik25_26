
module SNPS_CLOCK_GATE_HIGH_counter_d_W4_77 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  reg [3:0] count;
  wire [3:0] next_count;
  assign next_count = count + 1;

  always @(posedge CLK) begin
    if (EN && !TE) begin
      if (count == 4'b1111) begin
        count <= 4'b0000;
      end else begin
        count <= next_count;
      end
    end
  end

  assign ENCLK = count[3];

  initial begin
      // $sdf_annotate("CORDIC_Arch2v1_ASIC_fpu_syn_constraints_clk40.tcl_GATED_syn.sdf"); 
  end 

endmodule