
module crossbar_3x2 (
    input aclk,
    input aresetn,
    input [31:0] s_axis_0_tdata,
    input [31:0] s_axis_1_tdata,
    input [31:0] s_axis_2_tdata,
    input s_axis_0_tvalid,
    input s_axis_1_tvalid,
    input s_axis_2_tvalid,
    output s_axis_0_tready,
    output s_axis_1_tready,
    output s_axis_2_tready,
    output [31:0] m_axis_0_tdata,
    output [31:0] m_axis_1_tdata,
    output m_axis_0_tvalid,
    output m_axis_1_tvalid,
    input m_axis_0_tready,
    input m_axis_1_tready
);

// internal signals
reg [31:0] buffer_0;
reg [31:0] buffer_1;
reg [31:0] buffer_2;
reg [1:0] current_route;
reg [1:0] next_route;

// initialize buffers to zero
initial begin
    buffer_0 <= 0;
    buffer_1 <= 0;
    buffer_2 <= 0;
end

// compute next buffers
always @(*) begin
    buffer_0 <= (current_route == 0) ? s_axis_0_tdata :
                    (current_route == 1) ? s_axis_1_tdata :
                                         s_axis_2_tdata;
    buffer_1 <= (current_route == 0) ? s_axis_1_tdata :
                    (current_route == 1) ? s_axis_2_tdata :
                                         s_axis_0_tdata;
    buffer_2 <= (current_route == 0) ? s_axis_2_tdata :
                    (current_route == 1) ? s_axis_0_tdata :
                                         s_axis_1_tdata;
end

// compute current route
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        current_route <= 0;
    end else begin
        case (m_axis_0_tvalid)
            1: current_route <= (s_axis_1_tvalid || s_axis_2_tvalid) ? 1 :
                               (s_axis_2_tvalid) ? 2 :
                                                 current_route;
            0: case (m_axis_1_tvalid)
                1: current_route <= (s_axis_0_tvalid || s_axis_2_tvalid) ? 0 :
                               (s_axis_2_tvalid) ? 2 :
                                                 current_route;
                0: current_route <= (s_axis_0_tvalid || s_axis_1_tvalid) ? 0 :
                               (s_axis_1_tvalid) ? 1 :
                                                 current_route;
            endcase
        endcase
    end
end

// compute next route
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        next_route <= 0;
    end else begin
        case (current_route)
            0: next_route <= (s_axis_1_tvalid || s_axis_2_tvalid) ? 1 :
                               (s_axis_2_tvalid) ? 2 :
                                                 next_route;
            1: next_route <= (s_axis_0_tvalid || s_axis_2_tvalid) ? 0 :
                               (s_axis_2_tvalid) ? 2 :
                                                 next_route;
            2: next_route <= (s_axis_0_tvalid || s_axis_1_tvalid) ? 0 :
                               (s_axis_1_tvalid) ? 1 :
                                                 next_route;
            default: next_route <= next_route;
        endcase
    end
end

// assign outputs
assign s_axis_0_tready = !(m_axis_0_tvalid || m_axis_1_tvalid);
assign s_axis_1_tready = !(m_axis_0_tvalid || m_axis_1_tvalid);
assign s_axis_2_tready = !m_axis_0_tvalid;
assign m_axis_0_tdata = buffer_0;
assign m_axis_1_tdata = buffer_1;
assign m_axis_0_tvalid = (m_axis_0_tready) && ((s_axis_0_tvalid) || (s_axis_1_tvalid) || (s_axis_2_tvalid));
assign m_axis_1_tvalid = (m_axis_1_tready) && ((s_axis_0_tvalid) || (s_axis_1_tvalid) || (s_axis_2_tvalid));

endmodule