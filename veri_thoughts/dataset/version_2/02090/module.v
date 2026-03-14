
module dual_edge_triggered_flip_flop (
    input clk,
    input d,
    output q
);

reg q1, q2;

always @(posedge clk) // Only positive edge of clock
begin
    q1 <= d;
    q2 <= q1;
end

assign q = q2;

endmodule