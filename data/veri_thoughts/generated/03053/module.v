
module wasca_nios2_gen2_0_cpu_nios2_oci_td_mode (
    input [8:0] ctrl,
    output reg [3:0] td_mode
);

    always @(*) begin
        case (ctrl)
            9'b000000000: td_mode = 4'b0000; // No Trace
            9'b000000001: td_mode = 4'b0001; // Record Load Address
            9'b000000010: td_mode = 4'b0010; // Record Store Address
            9'b000000011: td_mode = 4'b0011; // Record Load Data
            9'b000000100: td_mode = 4'b0100; // Record Store Data
            default:       td_mode = 4'b0000; // No Trace
        endcase
    end

endmodule
