
module freq_divider (
    input clk, // Clock input
    input reset, // Asynchronous reset input
    output out_clk // Output clock signal with half the frequency of the input clock
);

reg Q1, Q2;

always @(posedge clk, negedge reset) begin
    if (!reset) begin
        Q1 <= 0;
        Q2 <= 0;
    end else begin
        Q1 <= ~Q1; // Toggle Q1 on the positive edge of clk
        Q2 <= Q1; // Assign Q2 to the toggled value of Q1
    end
end

assign out_clk = Q2; // Assign out_clk to the value of Q2

endmodule
