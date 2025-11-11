module minimac2_sync(
    input sys_clk,
    input phy_rx_clk,
    input phy_tx_clk,
    
    input [1:0] sys_rx_ready,
    output [1:0] sys_rx_done,
    output reg [10:0] sys_rx_count_0,
    output reg [10:0] sys_rx_count_1,
    
    input sys_tx_start,
    output sys_tx_done,
    input [10:0] sys_tx_count,
    
    output [1:0] phy_rx_ready,
    input [1:0] phy_rx_done,
    input [10:0] phy_rx_count_0,
    input [10:0] phy_rx_count_1,
    
    output phy_tx_start,
    input phy_tx_done,
    output reg [10:0] phy_tx_count
);

minimac2_psync rx_ready_0(
    .clk1(sys_clk),
    .i(sys_rx_ready[0]),
    .clk2(phy_rx_clk),
    .o(phy_rx_ready[0])
);
minimac2_psync rx_ready_1(
    .clk1(sys_clk),
    .i(sys_rx_ready[1]),
    .clk2(phy_rx_clk),
    .o(phy_rx_ready[1])
);
minimac2_psync rx_done_0(
    .clk1(phy_rx_clk),
    .i(phy_rx_done[0]),
    .clk2(sys_clk),
    .o(sys_rx_done[0])
);
minimac2_psync rx_done_1(
    .clk1(phy_rx_clk),
    .i(phy_rx_done[1]),
    .clk2(sys_clk),
    .o(sys_rx_done[1])
);
reg [10:0] sys_rx_count_0_r;
reg [10:0] sys_rx_count_1_r;
always @(posedge sys_clk) begin
    sys_rx_count_0_r <= phy_rx_count_0;
    sys_rx_count_0 <= sys_rx_count_0_r;
    sys_rx_count_1_r <= phy_rx_count_1;
    sys_rx_count_1 <= sys_rx_count_1_r;
end

minimac2_psync tx_start(
    .clk1(sys_clk),
    .i(sys_tx_start),
    .clk2(phy_tx_clk),
    .o(phy_tx_start)
);
minimac2_psync tx_done(
    .clk1(phy_tx_clk),
    .i(phy_tx_done),
    .clk2(sys_clk),
    .o(sys_tx_done)
);
reg [10:0] phy_tx_count_r;
always @(posedge phy_tx_clk) begin
    phy_tx_count_r <= sys_tx_count;
    phy_tx_count <= phy_tx_count_r;
end

endmodule

module minimac2_psync(
    input clk1,       // Source clock
    input i,          // Input signal in the source clock domain
    input clk2,       // Destination clock
    output reg o      // Output signal in the destination clock domain
);

    // Synchronization from clk1 to clk2 domain
    reg intermediate;
    reg [1:0] sync_reg; // Double flip-flop for synchronizing the signal

    // Pulse detection in clk1 domain
    reg i_reg;
    wire pulse; // Detected pulse

    always @(posedge clk1) begin
        i_reg <= i;
    end
    assign pulse = i & ~i_reg; // Detecting rising edge

    // Transfer the pulse to the clk2 domain
    always @(posedge clk2) begin
        if (pulse)
            intermediate <= 1'b1; // Set intermediate high if a pulse is detected
        else if (sync_reg[1])
            intermediate <= 1'b0; // Reset intermediate when the pulse has been acknowledged

        sync_reg <= {sync_reg[0], intermediate}; // Synchronize the intermediate signal
    end

    always @(posedge clk2) begin
        o <= sync_reg[1]; // Output the synchronized signal
    end

endmodule
