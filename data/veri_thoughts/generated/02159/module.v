module mux_2to1_pipeline(
    input a,
    input b,
    input sel_b1,
    output reg out_always,
    input clk
);

// Pipeline register
reg pipeline_reg;

// Register pipeline stage
always @(posedge clk) begin
    pipeline_reg <= sel_b1;
end

// Output logic
always @(*) begin
    if (pipeline_reg) begin
        out_always = b;
    end else begin
        out_always = a;
    end
end

endmodule