module up_down_counter (
    input clk,
    input reset,   // Synchronous active-high reset
    input load,    // Load value into counter when asserted
    input up_down, // Count up or down based on value
    output reg [15:0] q);

    always @(posedge clk) begin
        if (reset) begin
            q <= 16'd0;
        end else if (load) begin
            q <= {q[15:12], q[11:8], q[7:4], q[3:0]};
        end else if (up_down) begin
            q <= q + 16'd1;
        end else begin
            q <= q - 16'd1;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    input load,    // Load value into counter when asserted
    input up_down, // Count up or down based on value
    output [15:0] q);

    up_down_counter counter (
        .clk(clk),
        .reset(reset),
        .load(load),
        .up_down(up_down),
        .q(q)
    );

endmodule