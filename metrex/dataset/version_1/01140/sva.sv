// SVA for erx_remap. Bind this to the DUT instance(s).

module erx_remap_sva #(
  parameter AW = 32,
  parameter DW = 32,
  parameter PW = 104,
  parameter ID = 12'h808
)(
  input                clk,
  input                emesh_access_in,
  input  [PW-1:0]      emesh_packet_in,
  input  [1:0]         remap_mode,
  input  [11:0]        remap_sel,
  input  [11:0]        remap_pattern,
  input  [31:0]        remap_base,
  input                emesh_access_out,
  input  [PW-1:0]      emesh_packet_out
);

  // Derived constants
  localparam int unsigned COLID = ID[5:0];
  localparam int unsigned SHIFT = $clog2((COLID < 1) ? 1 : COLID);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Helpers
  function automatic [31:0] f_static(input [31:0] addr, input [11:0] sel, input [11:0] pat);
    f_static[31:20] = (sel & pat) | (~sel & addr[31:20]);
    f_static[19:0]  = addr[19:0];
  endfunction

  function automatic [31:0] f_dynamic(input [31:0] addr, input [31:0] base);
    automatic logic [31:0] colid_shift = ({26'b0, COLID} << 20);
    automatic logic [31:0] group_shift = ({26'b0, addr[31:26]} << SHIFT);
    f_dynamic = addr - colid_shift + base - group_shift;
  endfunction

  function automatic [31:0] f_mux(input [31:0] addr,
                                  input [1:0] mode,
                                  input [11:0] sel,
                                  input [11:0] pat,
                                  input [31:0] base);
    if (addr[31:20] == ID)             f_mux = addr;
    else if (mode == 2'b00)            f_mux = addr;
    else if (mode == 2'b01)            f_mux = f_static(addr, sel, pat);
    else                               f_mux = f_dynamic(addr, base);
  endfunction

  // Shorthands to slices
  function automatic [31:0] in_addr(input [PW-1:0] pkt);  in_addr = pkt[39:8];  endfunction
  function automatic [11:0] in_addr_hi12(input [PW-1:0] pkt); in_addr_hi12 = pkt[39:28]; endfunction

  // 1-cycle pipeline checks
  // Access pipe
  assert property (past_valid |-> emesh_access_out == $past(emesh_access_in))
    else $error("emesh_access_out not 1-cycle delayed version of emesh_access_in");

  // Packet framing (non-address fields passthrough)
  assert property (past_valid |-> (emesh_packet_out[103:40] == $past(emesh_packet_in[103:40]) &&
                                   emesh_packet_out[7:0]    == $past(emesh_packet_in[7:0])))
    else $error("Non-address fields not passed through with 1-cycle latency");

  // Address remap correctness
  assert property (past_valid |-> emesh_packet_out[39:8] ==
                              f_mux($past(in_addr(emesh_packet_in)),
                                    $past(remap_mode),
                                    $past(remap_sel),
                                    $past(remap_pattern),
                                    $past(remap_base)))
    else $error("Address remap mismatch");

  // Mode-specific and bypass checks
  // Bypass on ID match regardless of mode
  assert property (past_valid &&
                   ($past(in_addr(emesh_packet_in)[31:20]) == ID)
                   |-> emesh_packet_out[39:8] == $past(in_addr(emesh_packet_in)))
    else $error("ID bypass not honored");

  // Mode 00 (no remap) when no ID bypass
  assert property (past_valid &&
                   ($past(in_addr(emesh_packet_in)[31:20]) != ID) &&
                   ($past(remap_mode) == 2'b00)
                   |-> emesh_packet_out[39:8] == $past(in_addr(emesh_packet_in)))
    else $error("Mode 00 remap mismatch");

  // Mode 01 (static): lower 20 address bits must pass through when selected (no ID bypass)
  assert property (past_valid &&
                   ($past(in_addr(emesh_packet_in)[31:20]) != ID) &&
                   ($past(remap_mode) == 2'b01)
                   |-> emesh_packet_out[27:8] == $past(emesh_packet_in[27:8]))
    else $error("Static remap: lower 20 address bits not preserved");

  // Mode 01 (static): upper 12 bits must be masked/muxed correctly (no ID bypass)
  assert property (past_valid &&
                   ($past(in_addr(emesh_packet_in)[31:20]) != ID) &&
                   ($past(remap_mode) == 2'b01)
                   |-> emesh_packet_out[39:28] ==
                       (($past(remap_sel) & $past(remap_pattern)) |
                        (~$past(remap_sel) & $past(emesh_packet_in[39:28]))))
    else $error("Static remap: upper 12 address bits incorrect");

  // Sanity: outputs not X/Z if prior inputs known
  assert property (past_valid &&
                   !$isunknown($past({emesh_access_in, emesh_packet_in,
                                      remap_mode, remap_sel, remap_pattern, remap_base})))
                  |-> !$isunknown({emesh_access_out, emesh_packet_out}))
    else $error("Outputs contain X/Z while prior inputs were known");

  // Functional coverage
  cover property (past_valid && ($past(in_addr(emesh_packet_in)[31:20]) == ID));         // ID bypass
  cover property (past_valid && ($past(remap_mode) == 2'b00) &&
                  ($past(in_addr(emesh_packet_in)[31:20]) != ID));                        // mode 00 path
  cover property (past_valid && ($past(remap_mode) == 2'b01) &&
                  ($past(in_addr(emesh_packet_in)[31:20]) != ID));                        // static path
  cover property (past_valid && ($past(remap_mode)[1] == 1'b1) &&
                  ($past(in_addr(emesh_packet_in)[31:20]) != ID));                        // dynamic path (10/11)

  // Static remap extremes
  cover property (past_valid && ($past(remap_mode) == 2'b01) && ($past(remap_sel) == 12'h000));
  cover property (past_valid && ($past(remap_mode) == 2'b01) && ($past(remap_sel) == 12'hFFF));

  // Dynamic remap variety
  if (SHIFT > 0)
    cover property (past_valid && ($past(remap_mode)[1] == 1'b1) &&
                    ($past(in_addr(emesh_packet_in)[31:26]) != 6'h00));                   // exercise group_shift
  cover property (past_valid && ($past(remap_mode)[1] == 1'b1) &&
                  ($past(remap_base) != 32'h0));                                          // base offset used

endmodule

// Bind to all instances of erx_remap
bind erx_remap erx_remap_sva #(.AW(AW), .DW(DW), .PW(PW), .ID(ID))
  erx_remap_sva_i (
    .clk              (clk),
    .emesh_access_in  (emesh_access_in),
    .emesh_packet_in  (emesh_packet_in),
    .remap_mode       (remap_mode),
    .remap_sel        (remap_sel),
    .remap_pattern    (remap_pattern),
    .remap_base       (remap_base),
    .emesh_access_out (emesh_access_out),
    .emesh_packet_out (emesh_packet_out)
  );