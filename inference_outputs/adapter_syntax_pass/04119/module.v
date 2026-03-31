
module shift_register (
    input clk,
    input areset,
    input load,
    input ena,
    input [3:0] data,
    output [3:0] q
);

    reg [3:0] q;

    always @(posedge clk or negedge areset) begin
        if (!areset) begin
            q = 4'b0000;
        end else if (load) begin
            q = data;
        end else if (ena) begin
            q = {q[2:0], q[3]};
        end
    end

endmodule
