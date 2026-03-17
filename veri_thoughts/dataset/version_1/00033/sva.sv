module emesh_if_sva #(
    parameter AW = 32,
    parameter PW = 2*AW+40
) (
    input logic          clk,
    input logic          cmesh_ready_out,
    input logic          cmesh_access_out,
    input logic [PW-1:0] cmesh_packet_out,
    input logic          rmesh_ready_out,
    input logic          rmesh_access_out,
    input logic [PW-1:0] rmesh_packet_out,
    input logic          xmesh_ready_out,
    input logic          xmesh_access_out,
    input logic [PW-1:0] xmesh_packet_out,
    input logic          emesh_ready_out,
    input logic          emesh_access_out,
    input logic [PW-1:0] emesh_packet_out,
    input logic          cmesh_access_in,
    input logic [PW-1:0] cmesh_packet_in,
    input logic          cmesh_ready_in,
    input logic          rmesh_access_in,
    input logic [PW-1:0] rmesh_packet_in,
    input logic          rmesh_ready_in,
    input logic          xmesh_access_in,
    input logic [PW-1:0] xmesh_packet_in,
    input logic          xmesh_ready_in,
    input logic          emesh_access_in,
    input logic [PW-1:0] emesh_packet_in,
    input logic          emesh_ready_in
);

    // cmesh access is selected when emesh is active and packet bit 0 is set.
    check_cmesh_access_decode: assert property (
        @(posedge clk)
        cmesh_access_out == (emesh_access_in & emesh_packet_in[0])
    );

    // rmesh access is selected when emesh is active and packet bit 0 is clear.
    check_rmesh_access_decode: assert property (
        @(posedge clk)
        rmesh_access_out == (emesh_access_in & ~emesh_packet_in[0])
    );

    // xmesh access output is permanently tied low.
    check_xmesh_access_tied_low: assert property (
        @(posedge clk)
        xmesh_access_out == 1'b0
    );

    // cmesh packet output mirrors the emesh packet input.
    check_cmesh_packet_forward: assert property (
        @(posedge clk)
        cmesh_packet_out == emesh_packet_in
    );

    // rmesh packet output mirrors the emesh packet input.
    check_rmesh_packet_forward: assert property (
        @(posedge clk)
        rmesh_packet_out == emesh_packet_in
    );

    // xmesh packet output mirrors the emesh packet input.
    check_xmesh_packet_forward: assert property (
        @(posedge clk)
        xmesh_packet_out == emesh_packet_in
    );

    // emesh ready is the AND of all downstream ready inputs.
    check_emesh_ready_and: assert property (
        @(posedge clk)
        emesh_ready_out == (cmesh_ready_in & rmesh_ready_in & xmesh_ready_in)
    );

    // emesh access out is the AND of all mesh access inputs.
    check_emesh_access_and: assert property (
        @(posedge clk)
        emesh_access_out == (cmesh_access_in & rmesh_access_in & xmesh_access_in)
    );

    // emesh packet out follows the documented priority mux.
    check_emesh_packet_priority_mux: assert property (
        @(posedge clk)
        emesh_packet_out == (cmesh_access_in ? cmesh_packet_in :
                             rmesh_access_in ? rmesh_packet_in :
                                               xmesh_packet_in)
    );

    // cmesh ready deasserts only when cmesh is accessing and emesh is not ready.
    check_cmesh_ready_backpressure: assert property (
        @(posedge clk)
        cmesh_ready_out == ~(cmesh_access_in & ~emesh_ready_in)
    );

    // rmesh ready deasserts only under the implemented rmesh backpressure condition.
    check_rmesh_ready_backpressure: assert property (
        @(posedge clk)
        rmesh_ready_out == ~(rmesh_access_in & (~emesh_ready_in | ~cmesh_ready_in))
    );

    // xmesh ready deasserts only under the implemented xmesh backpressure condition.
    check_xmesh_ready_backpressure: assert property (
        @(posedge clk)
        xmesh_ready_out == ~(xmesh_access_in & (~emesh_ready_in | ~cmesh_access_in | ~rmesh_access_in))
    );

endmodule