module counter (
    input clk,
    input reset,      // Asynchronous active-high reset
    input up_down,    // Control input to select count direction
    output reg [2:0] q
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q <= 3'b000;
        end
        else if (up_down) begin
            q <= q + 1;
        end
        else begin
            q <= q - 1;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,      // Asynchronous active-high reset
    input up_down,    // Control input to select count direction
    output reg [2:0] q
);

    wire [2:0] q_internal;
    
    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .up_down(up_down),
        .q(q_internal)
    );
    
    always @* begin
        q = q_internal;
    end

endmodule