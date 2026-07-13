
module axi_protocol_converter(
    input wire aclk,
    input wire m_axi_arvalid,
    output reg m_axi_arready,
    input wire [31:0] m_axi_araddr,
    input wire [31:0] m_payload_i_reg,
    output wire [31:0] m_payload_o_reg,
    input wire si_rs_arvalid
);

    // Define states for the state machine
    localparam IDLE = 2'b00;
    localparam READ = 2'b01;
    localparam WRITE = 2'b10;

    // Define state registers
    reg [1:0] state_reg;
    reg [31:0] address_reg;
    reg [31:0] data_reg;

    // Define output registers
    reg [31:0] m_payload_o_reg_reg;

    // Default values
    assign m_payload_o_reg = m_payload_o_reg_reg;

    // State machine
    always @(posedge aclk) begin
        case (state_reg)
            IDLE: begin
                if (m_axi_arvalid) begin
                    address_reg <= m_axi_araddr;
                    state_reg <= READ;
                end
                else if (si_rs_arvalid) begin
                    address_reg <= m_axi_araddr;
                    data_reg <= m_payload_i_reg;
                    state_reg <= WRITE;
                end
            end
            READ: begin
                if (m_axi_arready) begin
                    m_axi_arready <= 0;
                    state_reg <= IDLE;
                end
                else begin
                    m_axi_arready <= 1;
                    state_reg <= READ;
                end
            end
            WRITE: begin
                if (m_axi_arready) begin
                    m_axi_arready <= 0;
                    state_reg <= IDLE;
                end
                else begin
                    m_payload_o_reg_reg <= data_reg;
                    m_axi_arready <= 1;
                    state_reg <= WRITE;
                end
            end
            default: state_reg <= IDLE;
        endcase
    end
endmodule