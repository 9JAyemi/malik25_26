module barrel_shifter_4bit (
    input clk, // Correctly included clock input in the module's port list
    input [3:0] A,
    input load,
    input reset,
    input [1:0] shift,
    input shift_dir, // 0 for left shift, 1 for right shift
    output reg [3:0] Q
);

always @(posedge clk) begin
    if (reset) begin
        Q <= 4'b0; // Reset the output Q to 0
    end else if (load) begin
        Q <= A; // Load the input A into Q
    end else begin
        case (shift)
            2'b00: Q <= Q; // No shift
            2'b01: begin
                // Shift once, direction based on shift_dir
                if (shift_dir) begin
                    // Right shift
                    Q <= {1'b0, Q[3:1]};
                end else begin
                    // Left shift
                    Q <= {Q[2:0], 1'b0};
                end
            end
            2'b10: begin
                // Shift twice, direction based on shift_dir
                if (shift_dir) begin
                    // Right shift
                    Q <= {2'b00, Q[3:2]};
                end else begin
                    // Left shift
                    Q <= {Q[1:0], 2'b00};
                end
            end
            2'b11: begin
                if (shift_dir) begin
                    // Right rotate
                    Q <= {Q[0], Q[3:1]};
                end else begin
                    // Left rotate
                    Q <= {Q[2:0], Q[3]};
                end
            end
        endcase
    end
end

endmodule
