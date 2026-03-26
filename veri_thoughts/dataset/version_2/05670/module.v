module johnson_counter (
    input clk,
    input rst,
    input ena,
    output reg [3:0] q
);

reg [3:0] q_next;

always @(posedge clk) begin
    if (rst) begin
        q <= 4'b0000;
    end
    else if (ena) begin
        q <= q_next;
    end
end

always @(*) begin
    q_next[0] = q[3] ^ ~q[1];
    q_next[1] = q[0] ^ ~q[2];
    q_next[2] = q[1] ^ ~q[3];
    q_next[3] = q[2] ^ ~q[0];
end

endmodule