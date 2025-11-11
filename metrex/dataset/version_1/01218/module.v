module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    input load,    // Load value into counter when asserted
    input up_down, // Count up or down based on value
    input [31:0] in, // Input vector for the transition detector
    output [7:0] q // 8-bit output from the functional module
);

    // Counter module with parallel load and up/down counting
    reg [15:0] count;
    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (load) begin
            count <= {in[15:12], in[23:20], in[31:28], in[27:24]};
        end else if (up_down) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end

    // Transition detector module using FSM architecture
    reg [31:0] prev_in;
    reg [31:0] transition;
    parameter IDLE = 2'b00;
    parameter DETECT = 2'b01;
    parameter OUTPUT = 2'b10;
    reg [1:0] state;
    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            prev_in <= 0;
            transition <= 0;
        end else begin
            case (state)
                IDLE: begin
                    if (in != prev_in) begin
                        state <= DETECT;
                        prev_in <= in;
                    end
                end
                DETECT: begin
                    if (in == prev_in) begin
                        state <= IDLE;
                        transition <= transition | prev_in;
                    end else begin
                        prev_in <= in;
                    end
                end
                OUTPUT: begin
                    state <= IDLE;
                    prev_in <= in;
                end
            endcase
        end
    end

    // Functional module to combine counter and transition detector outputs
    assign q = {count[3:0], count[7:4], count[11:8], count[15:12], transition[31:24], transition[23:16], transition[15:8], transition[7:0]};

endmodule