module vga_output_sva(
    input logic clk,
    input logic vga_hs,
    input logic vga_vs,
    input logic [4:0] vga_r,
    input logic [5:0] vga_g,
    input logic [4:0] vga_b,
    input logic [10:0] h_counter,
    input logic [9:0] v_counter
);

  localparam int H_RES = 640;
  localparam int V_RES = 480;
  localparam int H_SYNC_PULSE = 96;
  localparam int H_FRONT_PORCH = 16;
  localparam int H_BACK_PORCH = 48;
  localparam int V_SYNC_PULSE = 2;
  localparam int V_FRONT_PORCH = 10;
  localparam int V_BACK_PORCH = 33;

  localparam int H_TOTAL = H_RES + H_SYNC_PULSE + H_FRONT_PORCH + H_BACK_PORCH;
  localparam int V_TOTAL = V_RES + V_SYNC_PULSE + V_FRONT_PORCH + V_BACK_PORCH;

  localparam int H_SYNC_START = H_RES + H_FRONT_PORCH;
  localparam int H_SYNC_END = H_RES + H_FRONT_PORCH + H_SYNC_PULSE;
  localparam int V_SYNC_START = V_RES + V_FRONT_PORCH;
  localparam int V_SYNC_END = V_RES + V_FRONT_PORCH + V_SYNC_PULSE;

  localparam int COLOR_START = H_RES + H_FRONT_PORCH;
  localparam int COLOR_END = H_RES + H_FRONT_PORCH + 8;

  // h_counter is driven into the legal horizontal range on the next cycle.
  check_h_counter_bounded: assert property (
    @(posedge clk) disable iff (1'b0) 1'b1 |=> (h_counter <= H_TOTAL - 1)
  );

  // h_counter wraps to zero at or above the terminal horizontal count.
  check_h_counter_wraps: assert property (
    @(posedge clk) disable iff (1'b0) (h_counter >= H_TOTAL - 1) |=> (h_counter == 11'd0)
  );

  // h_counter increments by one below the terminal horizontal count.
  check_h_counter_increments: assert property (
    @(posedge clk) disable iff (1'b0) (h_counter < H_TOTAL - 1) |=> (h_counter == $past(h_counter) + 11'd1)
  );

  // v_counter is driven into the legal vertical range on the next cycle.
  check_v_counter_bounded: assert property (
    @(posedge clk) disable iff (1'b0) 1'b1 |=> (v_counter <= V_TOTAL - 1)
  );

  // v_counter wraps to zero at or above the terminal vertical count.
  check_v_counter_wraps: assert property (
    @(posedge clk) disable iff (1'b0) (v_counter >= V_TOTAL - 1) |=> (v_counter == 10'd0)
  );

  // v_counter increments by one below the terminal vertical count.
  check_v_counter_increments: assert property (
    @(posedge clk) disable iff (1'b0) (v_counter < V_TOTAL - 1) |=> (v_counter == $past(v_counter) + 10'd1)
  );

  // vga_hs is low during the programmed horizontal sync window.
  check_hsync_low_window: assert property (
    @(posedge clk) disable iff (1'b0)
      (h_counter >= H_SYNC_START && h_counter < H_SYNC_END) |=> (vga_hs == 1'b0)
  );

  // vga_hs is high outside the programmed horizontal sync window.
  check_hsync_high_outside_window: assert property (
    @(posedge clk) disable iff (1'b0)
      !(h_counter >= H_SYNC_START && h_counter < H_SYNC_END) |=> (vga_hs == 1'b1)
  );

  // vga_vs is low during the programmed vertical sync window.
  check_vsync_low_window: assert property (
    @(posedge clk) disable iff (1'b0)
      (v_counter >= V_SYNC_START && v_counter < V_SYNC_END) |=> (vga_vs == 1'b0)
  );

  // vga_vs is high outside the programmed vertical sync window.
  check_vsync_high_outside_window: assert property (
    @(posedge clk) disable iff (1'b0)
      !(v_counter >= V_SYNC_START && v_counter < V_SYNC_END) |=> (vga_vs == 1'b1)
  );

  // The color outputs are white in the programmed 8-cycle color window.
  check_color_white_window: assert property (
    @(posedge clk) disable iff (1'b0)
      (h_counter >= COLOR_START && h_counter < COLOR_END)
      |=> (vga_r == 5'd31 && vga_g == 6'd63 && vga_b == 5'd31)
  );

  // The color outputs are black outside the programmed 8-cycle color window.
  check_color_black_outside_window: assert property (
    @(posedge clk) disable iff (1'b0)
      !(h_counter >= COLOR_START && h_counter < COLOR_END)
      |=> (vga_r == 5'd0 && vga_g == 6'd0 && vga_b == 5'd0)
  );

endmodule