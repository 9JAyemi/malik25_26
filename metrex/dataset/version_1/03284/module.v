
module cross_domain_signal (
    input CLK_A,        // Clock for domain A
    input CLK_A_SEND,   // Signal from domain A to domain B
    output CLK_A_RECV,  // Signal from domain B received in domain A 
    input CLK_B,        // Clock for domain B
    output CLK_B_RECV,  // Signal from domain A received in domain B
    output ERR          // Error output
);

    reg a_send_sync = 0;
    reg b_send_sync = 0;
    reg a_send_sync_ff;
    reg b_send_sync_ff;

    assign CLK_A_RECV = b_send_sync_ff;
    assign CLK_B_RECV = a_send_sync_ff;

    always @(posedge CLK_A) begin
        a_send_sync <= CLK_A_SEND;
    end

    always @(posedge CLK_B) begin
        b_send_sync <= CLK_A_SEND;
    end

    always @(posedge CLK_A) begin
        b_send_sync_ff <= b_send_sync;
    end

    always @(posedge CLK_B) begin
        a_send_sync_ff <= a_send_sync;
    end

    assign ERR = (a_send_sync & b_send_sync) | (~a_send_sync & ~b_send_sync);

endmodule