

module clk_gen #(
    parameter res    = 20,    parameter phase  =  1     )(
    input      clk_i, input      rst_i,
    output     clk_o  );

  reg [res-1:0] cnt;

  assign clk_o = cnt[res-1];

  always @(posedge clk_i)
    cnt <= rst_i ? {res{1'b0}} : (cnt + phase);

endmodule
