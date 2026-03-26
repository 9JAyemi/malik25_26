
module delay_gate_4stage (
    input clk,
    input A,
    output X
);

    reg [3:0] delay_reg;
    wire delayed_A;

    assign delayed_A = delay_reg[3];

    always @(posedge clk) begin
        delay_reg <= {delay_reg[2:0], A};
    end

    assign X = delayed_A;

endmodule
