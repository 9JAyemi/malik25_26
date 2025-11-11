module decade_counter (
    input clk,
    input slowena,
    input reset,
    input pause,
    output reg [3:0] q
);

reg [3:0] johnson_q;
reg [3:0] next_johnson_q;
reg pause_count;

always @ (posedge clk) begin
    if (reset) begin
        johnson_q <= 4'b0000;
        q <= 4'b0000;
        pause_count <= 0;
    end else begin
        if (slowena) begin
            next_johnson_q[3] <= johnson_q[2];
            next_johnson_q[2] <= johnson_q[1];
            next_johnson_q[1] <= johnson_q[0];
            next_johnson_q[0] <= ~johnson_q[3] & ~johnson_q[2] & ~johnson_q[1] & ~johnson_q[0];
            johnson_q <= next_johnson_q;
        end
        
        if (pause) begin
            pause_count <= 1;
        end else if (pause_count > 0) begin
            pause_count <= pause_count + 1;
        end else begin
            q <= johnson_q;
        end
    end
end

endmodule

module top_module (
    input clk,
    input slowena,
    input reset,
    output [3:0] q
);

wire pause;
reg slow_clk;

assign pause = q == 4'b1001;

always @ (posedge clk) begin
    if (reset) begin
        slow_clk <= 1'b0;
    end else begin
        if (slowena) begin
            if (slow_clk) begin
                slow_clk <= 1'b0;
            end else begin
                slow_clk <= 1'b1;
            end
        end
    end
end

decade_counter counter (
    .clk(clk),
    .slowena(slow_clk),
    .reset(reset),
    .pause(pause),
    .q(q)
);

endmodule