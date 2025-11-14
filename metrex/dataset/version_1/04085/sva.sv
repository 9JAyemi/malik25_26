// SVA checker for OV7670Init
module ov7670init_sva (
  input  logic        clk,       // sampling clock (any TB clock)
  input  logic        rst_n,     // active-low disable; tie 1'b1 if unused
  input  logic [5:0]  index_i,
  input  logic [16:0] data_o
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [16:0] exp_data (logic [5:0] idx);
    unique case (idx)
      6'd0:    exp_data = {16'h1280, 1'b1};
      6'd1:    exp_data = {16'hf0f0, 1'b1};
      6'd2:    exp_data = {16'h1180, 1'b1};
      6'd3:    exp_data = {16'h1205, 1'b1};
      default: exp_data = {16'hffff, 1'b1};
    endcase
  endfunction

  // Core functional mapping
  a_map:       assert property (disable iff (!rst_n) data_o == exp_data(index_i));

  // Sanity/robustness checks
  a_out_known: assert property (disable iff (!rst_n) !$isunknown(data_o));
  a_in_known:  assert property (disable iff (!rst_n) !$isunknown(index_i));
  a_lsb_one:   assert property (disable iff (!rst_n) data_o[0] == 1'b1);
  a_default:   assert property (disable iff (!rst_n)
                                (index_i inside {[6'd4:6'd63]}) |-> (data_o == {16'hffff,1'b1}));

  // Coverage: each case item plus default space
  c_idx0:      cover  property (disable iff (!rst_n) index_i == 6'd0 && data_o == {16'h1280,1'b1});
  c_idx1:      cover  property (disable iff (!rst_n) index_i == 6'd1 && data_o == {16'hf0f0,1'b1});
  c_idx2:      cover  property (disable iff (!rst_n) index_i == 6'd2 && data_o == {16'h1180,1'b1});
  c_idx3:      cover  property (disable iff (!rst_n) index_i == 6'd3 && data_o == {16'h1205,1'b1});
  c_default:   cover  property (disable iff (!rst_n)
                                (index_i inside {[6'd4:6'd63]}) && data_o == {16'hffff,1'b1});

endmodule

// Example bind (tie rst_n high if no reset is needed):
// bind OV7670Init ov7670init_sva u_ov7670init_sva (.clk(tb_clk), .rst_n(1'b1), .index_i(index_i), .data_o(data_o));