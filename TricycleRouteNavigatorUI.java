import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.imageio.ImageIO;
import java.awt.*;
import java.sql.*;
import java.util.*;
import java.util.List;

/**
 * Tricycle Route Navigator UI
 */
public class TricycleRouteNavigatorUI extends JFrame {

    private static final String DEFAULT_START = "A. Marcelo St";
    private static final double AVG_SPEED_KM_PER_H = 10.0;

    private static final Color COLOR_BG_DARK = new Color(0x1E1E1E);
    private static final Color COLOR_BG_CARD = new Color(0xFFCE70);
    private static final Color COLOR_PRIMARY = new Color(0x7F3C0F);
    private static final Color COLOR_PRIMARY_HOVER = new Color(0x9B4A13);
    private static final Color COLOR_TEXT = new Color(0x1E1E1E);
    private static final Color COLOR_TEXT_ON_PRIMARY = new Color(0xFFCE70);

    private static final String NODE_MARCELO = "A. Marcelo St";
    private static final String NODE_DELMAR = "Delmar";
    private static final String NODE_OVERLAND = "Overland Dr";

    // SQLite DB file (created in working directory)
    private static final String DB_URL = "jdbc:sqlite:tricycle_routes.db";

    // graph + state
    private final Graph graph;
    private final java.util.List<String> allLocations;

    private CardLayout cardLayout;
    private JPanel mainPanel;

    // Home dropdowns
    private JComboBox<String> homeStartCombo;
    private JComboBox<String> homeDestCombo;

    // shared route state
    private java.util.List<PathResult> currentRoutes = new ArrayList<>();
    private String currentStart = DEFAULT_START;
    private String currentDestination = null;
    private int currentPathIndex = 0;

    private ShortestRoutePanel shortestRoutePanel;
    private PathDetailsPanel pathDetailsPanel;
    private GraphLayoutPanel graphLayoutPanel;

    // static map image
    private Image staticMapImage;

    // ---------- Graph model ----------
    static class Edge {
        final String from, to;
        final double distance;
        Edge(String f, String t, double d) { from = f; to = t; distance = d; }
    }

    static class Graph {
        final Map<String, java.util.List<Edge>> adj = new HashMap<>();
        void addEdge(String from, String to, double d) {
            adj.computeIfAbsent(from, k -> new ArrayList<>()).add(new Edge(from, to, d));
            adj.computeIfAbsent(to, k -> new ArrayList<>()).add(new Edge(to, from, d));
        }
        Set<String> nodes() { return adj.keySet(); }
        java.util.List<Edge> neighbors(String n) { return adj.getOrDefault(n, Collections.emptyList()); }

        PathResult dijkstra(String src, String dst) {
            if (!adj.containsKey(src) || !adj.containsKey(dst)) return null;
            Map<String, Double> dist = new HashMap<>();
            Map<String, String> prev = new HashMap<>();
            for (String n : adj.keySet()) dist.put(n, Double.POSITIVE_INFINITY);
            dist.put(src, 0.0);
            Set<String> vis = new HashSet<>();
            while (true) {
                String u = null; double best = Double.POSITIVE_INFINITY;
                for (var e : dist.entrySet()) {
                    if (!vis.contains(e.getKey()) && e.getValue() < best) {
                        best = e.getValue(); u = e.getKey();
                    }
                }
                if (u == null || best == Double.POSITIVE_INFINITY) break;
                if (u.equals(dst)) break;
                vis.add(u);
                for (Edge e : neighbors(u)) {
                    if (vis.contains(e.to)) continue;
                    double alt = dist.get(u) + e.distance;
                    if (alt < dist.get(e.to)) {
                        dist.put(e.to, alt); prev.put(e.to, u);
                    }
                }
            }
            if (dist.getOrDefault(dst, Double.POSITIVE_INFINITY) == Double.POSITIVE_INFINITY) return null;
            java.util.List<String> path = new ArrayList<>();
            for (String u = dst; u != null; u = prev.get(u)) {
                path.add(0, u);
                if (u.equals(src)) break;
            }
            return new PathResult(path, dist.get(dst));
        }

        // Simple k-shortest (no loops)
        java.util.List<PathResult> kShortestPaths(String src, String dst, int k) {
            PathResult first = dijkstra(src, dst);
            if (first == null) return Collections.emptyList();
            java.util.List<PathResult> results = new ArrayList<>();
            results.add(first);
            java.util.List<PathResult> cands = new ArrayList<>();

            for (int ki = 1; ki < k; ki++) {
                PathResult last = results.get(ki - 1);
                var lastPath = last.path;
                for (int i = 0; i < lastPath.size() - 1; i++) {
                    String spurNode = lastPath.get(i);
                    java.util.List<String> rootPath = lastPath.subList(0, i + 1);
                    java.util.List<Edge> removed = new ArrayList<>();

                    for (PathResult p : results) {
                        if (sharePrefix(p.path, rootPath, i)) {
                            String u = p.path.get(i), v = p.path.get(i + 1);
                            removedEdges(adj, removed, u, v);
                        }
                    }

                    PathResult spur = dijkstra(spurNode, dst);
                    if (spur != null) {
                        java.util.List<String> newPath = new ArrayList<>(rootPath);
                        newPath.addAll(spur.path.subList(1, spur.path.size()));
                        double d = pathDistance(newPath);
                        PathResult cand = new PathResult(newPath, d);
                        if (!containsPath(cands, cand) && !containsPath(results, cand)) {
                            cands.add(cand);
                        }
                    }
                    restoreEdges(adj, removed);
                }
                if (cands.isEmpty()) break;
                cands.sort(Comparator.comparingDouble(p -> p.distance));
                PathResult best = cands.remove(0);
                results.add(best);
                if (results.size() >= k) break;
            }
            return results;
        }

        // Detour/loop-allowed search (parameterized)
        java.util.List<PathResult> kShortestPathsAllowingDetours(String src, String dst, int k,
                                                                 double maxDistanceFactor,
                                                                 int maxHops,
                                                                 int maxVisitsPerNode) {
            PathResult shortest = dijkstra(src, dst);
            if (shortest == null) return Collections.emptyList();

            double maxDistance = shortest.distance * maxDistanceFactor;
            java.util.List<PathResult> results = new ArrayList<>();
            Set<String> seenPaths = new HashSet<>();

            class DFS {
                void run(String node, double dist, java.util.List<String> path, Map<String,Integer> visits) {
                    if (dist > maxDistance || path.size() > maxHops) return;
                    if (results.size() >= k * 8) return; // collect extras, prune later
                    if (node.equals(dst)) {
                        String key = String.join("->", path);
                        if (seenPaths.add(key)) results.add(new PathResult(new ArrayList<>(path), dist));
                        return;
                    }
                    for (Edge e : neighbors(node)) {
                        int vCount = visits.getOrDefault(e.to, 0);
                        if (vCount >= maxVisitsPerNode) continue;
                        path.add(e.to);
                        visits.put(e.to, vCount + 1);
                        run(e.to, dist + e.distance, path, visits);
                        visits.put(e.to, vCount);
                        path.remove(path.size() - 1);
                    }
                }
            }

            java.util.List<String> startPath = new ArrayList<>();
            startPath.add(src);
            Map<String,Integer> visits = new HashMap<>();
            visits.put(src, 1);
            new DFS().run(src, 0.0, startPath, visits);

            results.sort(Comparator.comparingDouble(p -> p.distance));
            if (results.size() > k) results.subList(k, results.size()).clear();
            return results;
        }

        private boolean sharePrefix(java.util.List<String> path, java.util.List<String> root, int idx) {
            if (path.size() <= idx) return false;
            for (int i = 0; i <= idx; i++) if (!path.get(i).equals(root.get(i))) return false;
            return true;
        }

        private static void removedEdges(Map<String, java.util.List<Edge>> adj,
                                         java.util.List<Edge> removed, String u, String v) {
            java.util.List<Edge> lu = new ArrayList<>(adj.getOrDefault(u, new ArrayList<>()));
            java.util.List<Edge> keepU = new ArrayList<>();
            for (Edge e : lu) if (e.to.equals(v)) removed.add(e); else keepU.add(e);
            adj.put(u, keepU);

            java.util.List<Edge> lv = new ArrayList<>(adj.getOrDefault(v, new ArrayList<>()));
            java.util.List<Edge> keepV = new ArrayList<>();
            for (Edge e : lv) if (e.to.equals(u)) removed.add(e); else keepV.add(e);
            adj.put(v, keepV);
        }

        private static void restoreEdges(Map<String, java.util.List<Edge>> adj, java.util.List<Edge> edges) {
            for (Edge e : edges) adj.computeIfAbsent(e.from, k -> new ArrayList<>()).add(e);
        }

        private double pathDistance(java.util.List<String> path) {
            if (path.size() < 2) return 0;
            double sum = 0;
            for (int i = 0; i < path.size() - 1; i++) {
                String u = path.get(i), v = path.get(i + 1);
                for (Edge e : neighbors(u)) if (e.to.equals(v)) { sum += e.distance; break; }
            }
            return sum;
        }

        private boolean containsPath(java.util.List<PathResult> list, PathResult t) {
            for (PathResult p : list) {
                if (p.path.size() == t.path.size()) {
                    boolean same = true;
                    for (int i = 0; i < p.path.size(); i++) {
                        if (!p.path.get(i).equals(t.path.get(i))) { same = false; break; }
                    }
                    if (same) return true;
                }
            }
            return false;
        }
    }

    static class PathResult {
        final java.util.List<String> path;
        final double distance;
        PathResult(java.util.List<String> p, double d) { path = p; distance = d; }
    }

    private static double estimateTimeMinutes(double d) {
        if (d <= 0) return 0;
        return d / AVG_SPEED_KM_PER_H * 60.0;
    }

    private static String formatPath(java.util.List<String> nodes) {
        return String.join(" → ", nodes);
    }

    private static boolean hasLoop(java.util.List<String> path) {
        Set<String> seen = new HashSet<>();
        for (String n : path) if (!seen.add(n)) return true;
        return false;
    }

    // ---------- icon helper ----------
    private ImageIcon loadTricycleIcon(int w, int h) {
        java.net.URL url = getClass().getResource("/tricycle.png");
        if (url == null) return null;
        ImageIcon raw = new ImageIcon(url);
        if (w > 0 && h > 0) {
            Image scaled = raw.getImage().getScaledInstance(w, h, Image.SCALE_SMOOTH);
            return new ImageIcon(scaled);
        }
        return raw;
    }

    private Image loadStaticMap(String path) {
        try {
            return ImageIO.read(Objects.requireNonNull(getClass().getResource(path)));
        } catch (Exception e) {
            System.err.println("Could not load static map: " + e.getMessage());
            return null;
        }
    }

    // ---------- ctor ----------
    public TricycleRouteNavigatorUI() {
        super("");
        this.graph = createGraph();
        syncGraphToDatabase(graph);

        this.allLocations = new ArrayList<>(graph.nodes());
        Collections.sort(allLocations);

        staticMapImage = loadStaticMap("/static-map.png");

        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setSize(1100, 650);
        setLocationRelativeTo(null);
        getContentPane().setBackground(COLOR_BG_DARK);

        cardLayout = new CardLayout();
        mainPanel = new JPanel(cardLayout);
        mainPanel.setBackground(COLOR_BG_DARK);

        HomePanel home = new HomePanel();
        shortestRoutePanel = new ShortestRoutePanel();
        pathDetailsPanel = new PathDetailsPanel();
        graphLayoutPanel = new GraphLayoutPanel(staticMapImage);

        mainPanel.add(home, "HOME");
        mainPanel.add(shortestRoutePanel, "ROUTE");
        mainPanel.add(pathDetailsPanel, "DETAILS");
        mainPanel.add(graphLayoutPanel, "GRAPH");

        setLayout(new BorderLayout());
        add(mainPanel, BorderLayout.CENTER);
    }

    // ---------- GRAPH ----------
    private static Graph createGraph() {
        Graph g = new Graph();

        // LEFT MAIN CORRIDOR
        g.addEdge("A. Marcelo St", "Delmar", 0.4);
        g.addEdge("Delmar", "Overland Dr", 0.5);
        g.addEdge("Overland Dr", "Bernabe Court", 0.5);

        // UPPER LOOP
        g.addEdge("Bernabe Court", "Sumilang", 0.9);
        g.addEdge("Sumilang", "San Miguel", 0.5);
        g.addEdge("San Miguel", "Lorenzo", 0.4);
        g.addEdge("Lorenzo", "Alviar", 0.3);
        g.addEdge("Alviar", "F. Zafra", 0.3);
        g.addEdge("San Miguel", "F. Zafra", 0.8);
        g.addEdge("San Miguel", "Metro Sotanghon", 0.2);

        // LOWER‑LEFT LEG (Vida removed)
        g.addEdge("Bernabe Court", "Sandiego 1st St", 0.2);
        g.addEdge("E. Cantillon", "Sebastian", 0.2);

        // CENTER TO RIGHT CORRIDOR
        g.addEdge("Bernabe Court", "F. Zafra", 0.5);
        g.addEdge("F. Zafra", "E. Cantillon", 0.5);
        g.addEdge("E. Cantillon", "Anneville Ave", 0.4);
        g.addEdge("Anneville Ave", "F. Alarcon", 0.5);

        // LOWER‑RIGHT ROW
        g.addEdge("Anneville Ave", "Sandiego 1st St", 0.2);
        g.addEdge("Sandiego 1st St", "Sandiego 2nd St", 0.2);
        g.addEdge("Sandiego 2nd St", "Sebastian", 0.2);

        return g;
    }

    // ---------- SQLite sync ----------
    private void syncGraphToDatabase(Graph g) {
        try (Connection conn = DriverManager.getConnection(DB_URL)) {
            if (conn == null) {
                System.err.println("Could not connect to SQLite database.");
                return;
            }

            try (Statement st = conn.createStatement()) {
                st.executeUpdate(
                        "CREATE TABLE IF NOT EXISTS edges (" +
                                "id INTEGER PRIMARY KEY AUTOINCREMENT," +
                                "start_point TEXT NOT NULL," +
                                "destination_point TEXT NOT NULL," +
                                "distance_km REAL NOT NULL)"
                );
            }

            try (Statement st = conn.createStatement()) {
                st.executeUpdate("DELETE FROM edges");
            }

            class Row { String from; String to; double dist; Row(String f, String t, double d){from=f;to=t;dist=d;} }
            List<Row> rows = new ArrayList<>();
            Set<String> seen = new HashSet<>();
            for (String u : g.adj.keySet()) {
                for (Edge e : g.neighbors(u)) {
                    String key = e.from.compareTo(e.to) < 0
                            ? e.from + "->" + e.to
                            : e.to + "->" + e.from;
                    if (seen.contains(key)) continue;
                    seen.add(key);
                    rows.add(new Row(e.from, e.to, e.distance));
                }
            }

            rows.sort((a, b) -> {
                int c = a.from.compareToIgnoreCase(b.from);
                if (c != 0) return c;
                return a.to.compareToIgnoreCase(b.to);
            });

            String sql = "INSERT INTO edges(start_point, destination_point, distance_km) VALUES (?,?,?)";
            try (PreparedStatement ps = conn.prepareStatement(sql)) {
                for (Row r : rows) {
                    ps.setString(1, r.from);
                    ps.setString(2, r.to);
                    ps.setDouble(3, r.dist);
                    ps.addBatch();
                }
                ps.executeBatch();
            }

        } catch (SQLException ex) {
            ex.printStackTrace();
        }
    }

    // ---------- common UI helpers ----------
    private JButton makePrimaryButton(String txt) {
        JButton b = new JButton(txt);
        b.setBackground(COLOR_PRIMARY);
        b.setForeground(COLOR_TEXT_ON_PRIMARY);
        b.setFocusPainted(false);
        b.setBorderPainted(false);
        b.setOpaque(true);
        b.setFont(b.getFont().deriveFont(Font.BOLD, 14f));
        b.setBorder(new EmptyBorder(8, 20, 8, 20));
        b.getModel().addChangeListener(e -> {
            if (b.getModel().isRollover()) b.setBackground(COLOR_PRIMARY_HOVER);
            else b.setBackground(COLOR_PRIMARY);
        });
        return b;
    }

    private JPanel makeHeader() {
        JPanel header = new JPanel(new BorderLayout());
        header.setOpaque(false);

        JLabel logo = new JLabel("");
        logo.setForeground(COLOR_TEXT);
        logo.setFont(new Font("SansSerif", Font.BOLD, 20));

        JPanel left = new JPanel(new FlowLayout(FlowLayout.LEFT, 0, 0));
        left.setOpaque(false);
        left.add(logo);

        JPanel right = new JPanel(new FlowLayout(FlowLayout.RIGHT, 16, 0));
        right.setOpaque(false);
        JLabel home = new JLabel("Home");
        JLabel find = new JLabel("Find");
        JLabel graphLbl = new JLabel("Graph");
        for (JLabel l : new JLabel[]{home, find, graphLbl}) {
            l.setForeground(COLOR_TEXT);
            l.setFont(new Font("SansSerif", Font.BOLD, 14));
            l.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
        }
        home.addMouseListener(new SimpleClickAdapter(() -> cardLayout.show(mainPanel, "HOME")));
        find.addMouseListener(new SimpleClickAdapter(() -> {
            if (currentDestination != null) cardLayout.show(mainPanel, "ROUTE");
            else cardLayout.show(mainPanel, "HOME");
        }));
        graphLbl.addMouseListener(new SimpleClickAdapter(() -> {
            graphLayoutPanel.refresh();
            cardLayout.show(mainPanel, "GRAPH");
        }));
        right.add(home); right.add(find); right.add(graphLbl);

        header.add(left, BorderLayout.WEST);
        header.add(right, BorderLayout.EAST);
        return header;
    }

    // ---------- Panels ----------

    private class HomePanel extends JPanel {
        HomePanel() {
            setLayout(new BorderLayout());
            setBackground(COLOR_BG_DARK);

            JPanel card = new JPanel(new BorderLayout());
            card.setBackground(COLOR_BG_CARD);
            card.setBorder(new EmptyBorder(24, 32, 32, 32));
            card.add(makeHeader(), BorderLayout.NORTH);

            JPanel center = new JPanel(new GridBagLayout());
            center.setOpaque(false);
            GridBagConstraints gc = new GridBagConstraints();
            gc.gridx = 0; gc.gridy = 0;
            gc.weightx = 1; gc.weighty = 1;
            gc.anchor = GridBagConstraints.CENTER;

            JPanel inner = new JPanel();
            inner.setOpaque(false);
            inner.setLayout(new BoxLayout(inner, BoxLayout.Y_AXIS));
            inner.setBorder(new EmptyBorder(20, 80, 20, 80));

            JLabel homeIcon = new JLabel(loadTricycleIcon(64, 48));
            homeIcon.setAlignmentX(Component.CENTER_ALIGNMENT);

            JLabel t1 = new JLabel("Begin Your Journey At");
            t1.setAlignmentX(Component.CENTER_ALIGNMENT);
            t1.setFont(new Font("SansSerif", Font.PLAIN, 20));
            t1.setForeground(COLOR_TEXT);

            JLabel t2 = new JLabel("Tricycle Route Navigator");
            t2.setAlignmentX(Component.CENTER_ALIGNMENT);
            t2.setFont(new Font("SansSerif", Font.BOLD, 28));
            t2.setForeground(COLOR_TEXT);

            JLabel startLabel = new JLabel("Select Your Starting Point:");
            startLabel.setAlignmentX(Component.CENTER_ALIGNMENT);
            startLabel.setFont(new Font("SansSerif", Font.BOLD, 18));
            startLabel.setForeground(COLOR_TEXT);
            startLabel.setBorder(new EmptyBorder(24, 0, 8, 0));

            homeStartCombo = new JComboBox<>(allLocations.toArray(new String[0]));
            homeStartCombo.setMaximumSize(new Dimension(260, 40));
            homeStartCombo.setBackground(COLOR_PRIMARY);
            homeStartCombo.setForeground(COLOR_TEXT_ON_PRIMARY);
            homeStartCombo.setFont(new Font("SansSerif", Font.BOLD, 14));
            ((JLabel) homeStartCombo.getRenderer()).setHorizontalAlignment(SwingConstants.CENTER);
            homeStartCombo.setSelectedItem(DEFAULT_START);

            JLabel destLabel = new JLabel("Select Your Destination:");
            destLabel.setAlignmentX(Component.CENTER_ALIGNMENT);
            destLabel.setFont(new Font("SansSerif", Font.BOLD, 18));
            destLabel.setForeground(COLOR_TEXT);
            destLabel.setBorder(new EmptyBorder(16, 0, 8, 0));

            homeDestCombo = new JComboBox<>(allLocations.toArray(new String[0]));
            homeDestCombo.setMaximumSize(new Dimension(260, 40));
            homeDestCombo.setBackground(COLOR_PRIMARY);
            homeDestCombo.setForeground(COLOR_TEXT_ON_PRIMARY);
            homeDestCombo.setFont(new Font("SansSerif", Font.BOLD, 14));
            ((JLabel) homeDestCombo.getRenderer()).setHorizontalAlignment(SwingConstants.CENTER);
            homeDestCombo.setSelectedItem("F. Alarcon");

            JButton findBtn = makePrimaryButton("Find");
            findBtn.setAlignmentX(Component.CENTER_ALIGNMENT);
            findBtn.addActionListener(e -> findRoutesFromHome());

            JButton graphBtn = makePrimaryButton("View Graph Layout");
            graphBtn.setAlignmentX(Component.CENTER_ALIGNMENT);
            graphBtn.addActionListener(e -> {
                graphLayoutPanel.refresh();
                cardLayout.show(mainPanel, "GRAPH");
            });

            inner.add(homeIcon);
            inner.add(Box.createVerticalStrut(4));
            inner.add(t1);
            inner.add(t2);
            inner.add(startLabel);
            inner.add(homeStartCombo);
            inner.add(destLabel);
            inner.add(homeDestCombo);
            inner.add(Box.createVerticalStrut(16));
            inner.add(findBtn);
            inner.add(Box.createVerticalStrut(8));
            inner.add(graphBtn);

            center.add(inner, gc);
            card.add(center, BorderLayout.CENTER);

            add(card, BorderLayout.CENTER);
        }
    }

    private class ShortestRoutePanel extends JPanel {
        private JLabel startValueLabel;
        private JLabel destValueLabel;
        private JLabel pathLabel, distLabel, timeLabel;
        private JRadioButton rb1, rb2, rb3;

        ShortestRoutePanel() {
            setLayout(new BorderLayout());
            setBackground(COLOR_BG_DARK);

            JPanel card = new JPanel(new BorderLayout());
            card.setBackground(COLOR_BG_CARD);
            card.setBorder(new EmptyBorder(24, 32, 32, 32));
            card.add(makeHeader(), BorderLayout.NORTH);

            JPanel center = new JPanel(new GridBagLayout());
            center.setOpaque(false);
            GridBagConstraints gc = new GridBagConstraints();
            gc.gridx = 0; gc.gridy = 0;
            gc.weightx = 1; gc.weighty = 1;
            gc.anchor = GridBagConstraints.CENTER;

            JPanel inner = new JPanel();
            inner.setOpaque(false);
            inner.setLayout(new BoxLayout(inner, BoxLayout.Y_AXIS));
            inner.setBorder(new EmptyBorder(16, 80, 16, 80));

            JLabel routeIcon = new JLabel(loadTricycleIcon(48, 36));
            routeIcon.setAlignmentX(Component.CENTER_ALIGNMENT);

            JLabel y = new JLabel("You Are Now In");
            y.setAlignmentX(Component.CENTER_ALIGNMENT);
            y.setFont(new Font("SansSerif", Font.PLAIN, 18));
            y.setForeground(COLOR_TEXT);

            JLabel title = new JLabel("Shortest Route Graph");
            title.setAlignmentX(Component.CENTER_ALIGNMENT);
            title.setFont(new Font("SansSerif", Font.BOLD, 26));
            title.setForeground(COLOR_TEXT);

            JPanel startRow = new JPanel(new FlowLayout(FlowLayout.CENTER, 8, 0));
            startRow.setOpaque(false);
            JLabel startLbl = new JLabel("Starting Point:");
            startLbl.setForeground(COLOR_TEXT);
            startLbl.setFont(new Font("SansSerif", Font.BOLD, 16));
            startValueLabel = new JLabel("-");
            startValueLabel.setForeground(COLOR_TEXT);
            startValueLabel.setFont(new Font("SansSerif", Font.BOLD, 16));
            startRow.add(startLbl); startRow.add(startValueLabel);

            JPanel destRow = new JPanel(new FlowLayout(FlowLayout.CENTER, 8, 0));
            destRow.setOpaque(false);
            JLabel destLbl = new JLabel("Destination:");
            destLbl.setForeground(COLOR_TEXT);
            destLbl.setFont(new Font("SansSerif", Font.BOLD, 16));
            destValueLabel = new JLabel("-");
            destValueLabel.setForeground(COLOR_TEXT);
            destValueLabel.setFont(new Font("SansSerif", Font.BOLD, 16));
            destRow.add(destLbl); destRow.add(destValueLabel);

            JPanel radioRow = new JPanel(new FlowLayout(FlowLayout.CENTER, 16, 0));
            radioRow.setOpaque(false);
            JLabel planeLbl = new JLabel("Select Route:");
            planeLbl.setForeground(COLOR_TEXT);
            planeLbl.setFont(new Font("SansSerif", Font.PLAIN, 14));
            rb1 = new JRadioButton("Path 1 (Shortest)");
            rb2 = new JRadioButton("Path 2 (Short)");
            rb3 = new JRadioButton("Path 3 (Long)");
            for (JRadioButton rb : new JRadioButton[]{rb1, rb2, rb3}) {
                rb.setOpaque(false);
                rb.setForeground(COLOR_TEXT);
                rb.setFont(new Font("SansSerif", Font.PLAIN, 14));
            }
            ButtonGroup group = new ButtonGroup();
            group.add(rb1); group.add(rb2); group.add(rb3);
            rb1.setSelected(true);
            rb1.addActionListener(e -> showPath(0));
            rb2.addActionListener(e -> showPath(1));
            rb3.addActionListener(e -> showPath(2));
            radioRow.add(planeLbl); radioRow.add(rb1); radioRow.add(rb2); radioRow.add(rb3);

            pathLabel = new JLabel("Shortest Path: -");
            pathLabel.setAlignmentX(Component.CENTER_ALIGNMENT);
            pathLabel.setFont(new Font("SansSerif", Font.PLAIN, 16));
            pathLabel.setForeground(COLOR_TEXT);
            pathLabel.setBorder(new EmptyBorder(16, 0, 4, 0));

            distLabel = new JLabel("Total Distance: -");
            distLabel.setAlignmentX(Component.CENTER_ALIGNMENT);
            distLabel.setFont(new Font("SansSerif", Font.PLAIN, 16));
            distLabel.setForeground(COLOR_TEXT);

            timeLabel = new JLabel("Estimated Time: -");
            timeLabel.setAlignmentX(Component.CENTER_ALIGNMENT);
            timeLabel.setFont(new Font("SansSerif", Font.PLAIN, 16));
            timeLabel.setForeground(COLOR_TEXT);

            JPanel btnRow = new JPanel(new FlowLayout(FlowLayout.CENTER, 40, 16));
            btnRow.setOpaque(false);
            JButton detailsBtn = makePrimaryButton("Path Details");
            JButton graphBtn = makePrimaryButton("Graph");
            detailsBtn.addActionListener(e -> {
                pathDetailsPanel.refresh();
                cardLayout.show(mainPanel, "DETAILS");
            });
            graphBtn.addActionListener(e -> {
                graphLayoutPanel.refresh();
                cardLayout.show(mainPanel, "GRAPH");
            });
            btnRow.add(detailsBtn); btnRow.add(graphBtn);

            inner.add(routeIcon);
            inner.add(Box.createVerticalStrut(4));
            inner.add(y);
            inner.add(title);
            inner.add(startRow);
            inner.add(destRow);
            inner.add(Box.createVerticalStrut(4));
            inner.add(radioRow);
            inner.add(pathLabel);
            inner.add(distLabel);
            inner.add(timeLabel);
            inner.add(btnRow);

            center.add(inner, gc);
            card.add(center, BorderLayout.CENTER);
            add(card, BorderLayout.CENTER);
        }

        void refresh() {
            startValueLabel.setText(currentStart != null ? currentStart : "-");
            destValueLabel.setText(currentDestination != null ? currentDestination : "-");
            updateLabels();
        }

        private boolean isMarceloToDelmar() {
            return NODE_MARCELO.equals(currentStart) && NODE_DELMAR.equals(currentDestination);
        }
        private boolean isMarceloToOverland() {
            return NODE_MARCELO.equals(currentStart) && NODE_OVERLAND.equals(currentDestination);
        }

        // Hardcoded detour variants to guarantee 3 distinct paths for Marcelo->Delmar
        private java.util.List<PathResult> manualMarceloToDelmar() {
            java.util.List<PathResult> list = new ArrayList<>();
            // P1: direct
            list.add(new PathResult(List.of(
                    NODE_MARCELO, NODE_DELMAR
            ), distanceForPath(List.of(NODE_MARCELO, NODE_DELMAR))));

            // P2: Marcelo -> Delmar -> Overland -> Bernabe -> Overland -> Delmar (loop detour)
            list.add(new PathResult(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    NODE_OVERLAND, NODE_DELMAR
            ), distanceForPath(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    NODE_OVERLAND, NODE_DELMAR
            ))));

            // P3: bigger detour via right and back
            list.add(new PathResult(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    "F. Zafra", "E. Cantillon", "Anneville Ave", "Sandiego 1st St",
                    "Bernabe Court", NODE_OVERLAND, NODE_DELMAR
            ), distanceForPath(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    "F. Zafra", "E. Cantillon", "Anneville Ave", "Sandiego 1st St",
                    "Bernabe Court", NODE_OVERLAND, NODE_DELMAR
            ))));

            list.sort(Comparator.comparingDouble(p -> p.distance));
            return list;
        }

        // Hardcoded detour variants for Marcelo->Overland
        private java.util.List<PathResult> manualMarceloToOverland() {
            java.util.List<PathResult> list = new ArrayList<>();
            // P1 direct
            list.add(new PathResult(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND
            ), distanceForPath(List.of(NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND))));

            // P2 small loop through Bernabe
            list.add(new PathResult(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    NODE_OVERLAND
            ), distanceForPath(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    NODE_OVERLAND
            ))));

            // P3 longer detour via F. Zafra
            list.add(new PathResult(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    "F. Zafra", "Bernabe Court", NODE_OVERLAND
            ), distanceForPath(List.of(
                    NODE_MARCELO, NODE_DELMAR, NODE_OVERLAND, "Bernabe Court",
                    "F. Zafra", "Bernabe Court", NODE_OVERLAND
            ))));

            list.sort(Comparator.comparingDouble(p -> p.distance));
            return list;
        }

        private double distanceForPath(List<String> nodes) {
            double sum = 0;
            for (int i = 0; i < nodes.size() - 1; i++) {
                String u = nodes.get(i), v = nodes.get(i + 1);
                double d = 0;
                for (Edge e : graph.neighbors(u)) if (e.to.equals(v)) { d = e.distance; break; }
                sum += d;
            }
            return sum;
        }

        private void recalcRoutes() {
            if (currentStart == null || currentDestination == null) return;

            if (isMarceloToDelmar()) {
                currentRoutes = manualMarceloToDelmar();
            } else if (isMarceloToOverland()) {
                currentRoutes = manualMarceloToOverland();
            } else {
                java.util.List<PathResult> base = graph.kShortestPaths(currentStart, currentDestination, 3);
                currentRoutes = new ArrayList<>(base);

                int target = 3;
                if (currentRoutes.size() < target) {
                    java.util.List<PathResult> detours = graph.kShortestPathsAllowingDetours(
                            currentStart, currentDestination, 12, 4.0, 16, 3
                    );
                    for (PathResult pr : detours) {
                        if (!graph.containsPath(currentRoutes, pr)) {
                            currentRoutes.add(pr);
                            if (currentRoutes.size() >= target) break;
                        }
                    }
                }
                currentRoutes.sort(Comparator.comparingDouble(p -> p.distance));
                if (currentRoutes.size() > target) currentRoutes.subList(target, currentRoutes.size()).clear();
            }

            currentPathIndex = 0;
            rb1.setSelected(true);
            updateLabels();
            graphLayoutPanel.startPathAnimation();
        }

        private void showPath(int idx) {
            if (currentRoutes == null || idx >= currentRoutes.size()) return;
            currentPathIndex = idx;
            updateLabels();
            graphLayoutPanel.startPathAnimation();
        }

        private void updateLabels() {
            if (currentRoutes == null || currentRoutes.isEmpty() ||
                    currentPathIndex >= currentRoutes.size()) {
                pathLabel.setText("Shortest Path: -");
                distLabel.setText("Total Distance: -");
                timeLabel.setText("Estimated Time: -");
                return;
            }
            PathResult pr = currentRoutes.get(currentPathIndex);

            String labelPrefix;
            if (currentPathIndex == 0) labelPrefix = "Path 1 (Shortest)";
            else if (currentPathIndex == 1) labelPrefix = "Path 2 (Short)";
            else labelPrefix = "Path 3 (Long)";
            if (hasLoop(pr.path)) labelPrefix += " [Detour]";

            pathLabel.setText(labelPrefix + ": " + formatPath(pr.path));
            distLabel.setText(String.format("Total Distance: %.1f Km", pr.distance));
            double mins = estimateTimeMinutes(pr.distance);
            timeLabel.setText(String.format("Estimated Time: %.0f–%.0f Minutes",
                    Math.floor(mins * 0.8), Math.ceil(mins * 1.2)));
        }
    }

    private class PathDetailsPanel extends JPanel {
        private JTextArea area;
        PathDetailsPanel() {
            setLayout(new BorderLayout());
            setBackground(COLOR_BG_DARK);

            JPanel card = new JPanel(new BorderLayout());
            card.setBackground(COLOR_BG_CARD);
            card.setBorder(new EmptyBorder(24, 32, 32, 32));
            card.add(makeHeader(), BorderLayout.NORTH);

            JPanel center = new JPanel(new BorderLayout());
            center.setOpaque(false);
            center.setBorder(new EmptyBorder(20, 60, 20, 60));

            JLabel detailsIcon = new JLabel(loadTricycleIcon(48, 36));

            JLabel y = new JLabel("You Are Now In");
            y.setHorizontalAlignment(SwingConstants.CENTER);
            y.setFont(new Font("SansSerif", Font.PLAIN, 18));
            y.setForeground(COLOR_TEXT);

            JLabel title = new JLabel("Path Details");
            title.setHorizontalAlignment(SwingConstants.CENTER);
            title.setFont(new Font("SansSerif", Font.BOLD, 26));
            title.setForeground(COLOR_TEXT);

            JPanel top = new JPanel();
            top.setOpaque(false);
            top.setLayout(new BoxLayout(top, BoxLayout.Y_AXIS));
            detailsIcon.setAlignmentX(Component.CENTER_ALIGNMENT);
            y.setAlignmentX(Component.CENTER_ALIGNMENT);
            title.setAlignmentX(Component.CENTER_ALIGNMENT);
            top.add(detailsIcon);
            top.add(Box.createVerticalStrut(4));
            top.add(y);
            top.add(title);

            area = new JTextArea();
            area.setEditable(false);
            area.setBackground(COLOR_PRIMARY);
            area.setForeground(COLOR_TEXT_ON_PRIMARY);
            area.setFont(new Font("SansSerif", Font.PLAIN, 16));
            area.setMargin(new Insets(8, 10, 8, 10));

            JPanel btnRow = new JPanel(new FlowLayout(FlowLayout.CENTER, 40, 16));
            btnRow.setOpaque(false);
            JButton back = makePrimaryButton("Back");
            JButton graphBtn = makePrimaryButton("Graph");
            back.addActionListener(e -> {
                shortestRoutePanel.refresh();
                cardLayout.show(mainPanel, "ROUTE");
            });
            graphBtn.addActionListener(e -> {
                graphLayoutPanel.refresh();
                cardLayout.show(mainPanel, "GRAPH");
            });
            btnRow.add(back); btnRow.add(graphBtn);

            center.add(top, BorderLayout.NORTH);
            center.add(new JScrollPane(area), BorderLayout.CENTER);
            center.add(btnRow, BorderLayout.SOUTH);

            card.add(center, BorderLayout.CENTER);
            add(card, BorderLayout.CENTER);
        }

        void refresh() {
            if (currentRoutes == null || currentRoutes.isEmpty()) {
                area.setText("No path selected.");
                return;
            }
            if (currentPathIndex >= currentRoutes.size()) currentPathIndex = 0;
            PathResult pr = currentRoutes.get(currentPathIndex);
            StringBuilder sb = new StringBuilder();
            List<String> n = pr.path;
            for (int i = 0; i < n.size() - 1; i++) {
                String u = n.get(i), v = n.get(i + 1);
                double d = 0;
                for (Edge e : graph.neighbors(u)) if (e.to.equals(v)) { d = e.distance; break; }
                sb.append(String.format("%s To %s - %.1f Km%n", u, v, d));
            }
            if (hasLoop(pr.path)) sb.append("\nNote: This path includes a detour.\n");
            area.setText(sb.toString());
            area.setCaretPosition(0);
        }
    }

    // Mini map panel with static background and original coords
    private class MiniMapPanel extends JPanel {
        private final Map<String, Point> coords = new HashMap<>();
        private final int baseW = 1262; // native image width
        private final int baseH = 700;  // native image height
        private final Image mapImg;

        // animation state for highlighted path
        private javax.swing.Timer animationTimer;
        private double animationProgress = 0.0; // 0.0 .. 1.0

        MiniMapPanel(Image mapImg) {
            this.mapImg = mapImg;
            setBackground(COLOR_PRIMARY);

            // DO NOT CHANGE OTHER NODES OR THEIR POSITIONS
            coords.put("A. Marcelo St",  new Point(65, 470));
            coords.put("Delmar",         new Point(360, 360));
            coords.put("Overland Dr",    new Point(415, 330));
            coords.put("Bernabe Court",  new Point(640, 285));
            coords.put("F. Zafra",       new Point(990, 300));
            coords.put("Alviar",         new Point(960, 165));
            coords.put("San Miguel",     new Point(840, 85));
            coords.put("Sumilang",       new Point(790, 40));
            coords.put("Lorenzo",        new Point(880, 145));
            coords.put("E. Cantillon",   new Point(720, 680));
            coords.put("Anneville Ave",  new Point(1000, 430));
            coords.put("F. Alarcon",     new Point(1000, 380));
            coords.put("Metro Sotanghon",  new Point(990, 90));
            coords.put("Sandiego 1st St",  new Point(770, 490));
            coords.put("Sandiego 2nd St",  new Point(680, 550));
            coords.put("Sebastian",        new Point(845, 610));

            createAnimationTimer();
        }

        private void createAnimationTimer() {
            animationTimer = new javax.swing.Timer(33, e -> {
                animationProgress += 0.01;
                if (animationProgress >= 1.0) {
                    animationProgress = 1.0;
                    animationTimer.stop();
                }
                repaint();
            });
        }

        void restartAnimation() {
            animationProgress = 0.0;
            if (animationTimer.isRunning()) {
                animationTimer.stop();
            }
            animationTimer.start();
        }

        private static class Bubble {
            Rectangle rect;
            Bubble(Rectangle r) { rect = r; }
        }

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            Graphics2D g2 = (Graphics2D) g.create();
            g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);

            int w = getWidth(), h = getHeight();
            double sx = w / (double) baseW, sy = h / (double) baseH;

            if (mapImg != null) {
                g2.drawImage(mapImg, 0, 0, w, h, this);
            } else {
                g2.setColor(COLOR_PRIMARY);
                g2.fillRect(0, 0, w, h);
            }

            java.util.function.Function<String, Point> P = name -> {
                Point p = coords.getOrDefault(name, new Point(0, 0));
                return new Point((int) Math.round(p.x * sx), (int) Math.round(p.y * sy));
            };

            int nodeRadius    = Math.max(6,  h / 60);
            int bubbleHeight  = Math.max(14, h / 40);
            int bubbleWidth   = Math.max(46, w / 35);
            int bubbleArc     = bubbleHeight / 2;

            // Raised the bubbles to avoid covering the 0.3km/0.8km labels
            int bubbleOffsetBase  = nodeRadius + bubbleHeight + Math.max(6, h / 55);
            int labelOffsetY  = nodeRadius + 12;

            g2.setStroke(new BasicStroke(Math.max(1f, h / 360f)));
            Color edgeColor = new Color(90, 70, 50, 160);

            java.util.Map<String, Rectangle> labelRects = new HashMap<>();

            g2.setFont(new Font("SansSerif", Font.BOLD, Math.max(11, h / 42)));
            FontMetrics tmpFm = g2.getFontMetrics();

            for (String name : graph.nodes()) {
                Point p = P.apply(name);
                int textWidth = tmpFm.stringWidth(name);
                int textHeight = tmpFm.getHeight();
                int textX = p.x - textWidth / 2;
                int textY = p.y + labelOffsetY;
                textY = Math.min(h - tmpFm.getDescent() - 4, textY);
                int bgX = textX - 4;
                int bgY = textY - tmpFm.getAscent() - 2;
                int bgW = textWidth + 8;
                int bgH = textHeight;
                labelRects.put(name, new Rectangle(bgX, bgY, bgW, bgH));
            }

            java.util.List<Bubble> bubbles = new ArrayList<>();

            // ----- all edges + distance bubbles -----
            Set<String> drawnPairs = new HashSet<>();
            g2.setFont(new Font("SansSerif", Font.PLAIN, Math.max(10, h / 55)));
            FontMetrics fm = g2.getFontMetrics();

            for (String u : graph.nodes()) {
                for (Edge e : graph.neighbors(u)) {
                    String key = e.from.compareTo(e.to) < 0
                            ? e.from + "->" + e.to
                            : e.to + "->" + e.from;
                    if (drawnPairs.contains(key)) continue;
                    drawnPairs.add(key);

                    Point p1 = P.apply(e.from), p2 = P.apply(e.to);

                    g2.setColor(edgeColor);
                    g2.drawLine(p1.x, p1.y, p2.x, p2.y);

                    String distText = String.format("%.1f km", e.distance);
                    int mx = (p1.x + p2.x) / 2;
                    int my = (p1.y + p2.y) / 2;

                    double dx = p2.x - p1.x;
                    double dy = p2.y - p1.y;
                    double len = Math.sqrt(dx * dx + dy * dy);
                    double nx = 0, ny = -1;
                    if (len > 0) {
                        nx = -dy / len;
                        ny =  dx / len;
                    }

                    int chosenBx = 0, chosenBy = 0;
                    Rectangle chosenRect = null;

                    int[] stepDirs = {0, 1, -1, 2, -2};
                    for (int step : stepDirs) {
                        double bubbleOffset = bubbleOffsetBase + step * (bubbleHeight * 0.7);
                        int bx = mx + (int) (nx * bubbleOffset);
                        int by = my + (int) (ny * bubbleOffset);

                        by = Math.max(bubbleHeight, Math.min(h - bubbleHeight, by));
                        bx = Math.max(bubbleWidth / 2, Math.min(w - bubbleWidth / 2, bx));

                        Rectangle rect = new Rectangle(
                                bx - bubbleWidth / 2,
                                by - bubbleHeight / 2,
                                bubbleWidth,
                                bubbleHeight
                        );

                        boolean collides = false;

                        for (Bubble b : bubbles) {
                            if (b.rect.intersects(rect)) {
                                collides = true;
                                break;
                            }
                        }
                        if (collides) continue;

                        for (Rectangle lr : labelRects.values()) {
                            if (rect.intersects(lr)) {
                                collides = true;
                                break;
                            }
                        }
                        if (collides) continue;

                        chosenBx = bx;
                        chosenBy = by;
                        chosenRect = rect;
                        break;
                    }

                    if (chosenRect == null) {
                        double bubbleOffset = bubbleOffsetBase + bubbleHeight * 1.4;
                        chosenBx = mx + (int) (nx * bubbleOffset);
                        chosenBy = my + (int) (ny * bubbleOffset);
                        chosenBy = Math.max(bubbleHeight, Math.min(h - bubbleHeight, chosenBy));
                        chosenBx = Math.max(bubbleWidth / 2, Math.min(w - bubbleWidth / 2, chosenBx));
                        chosenRect = new Rectangle(
                                chosenBx - bubbleWidth / 2,
                                chosenBy - bubbleHeight / 2,
                                bubbleWidth,
                                bubbleHeight
                        );
                    }

                    bubbles.add(new Bubble(chosenRect));

                    g2.setColor(new Color(0, 0, 0, 170));
                    g2.fillRoundRect(chosenRect.x, chosenRect.y,
                            chosenRect.width, chosenRect.height, bubbleArc, bubbleArc);

                    g2.setColor(new Color(240, 240, 240));
                    int tx = chosenRect.x + (chosenRect.width - fm.stringWidth(distText)) / 2;
                    int ty = chosenRect.y + (chosenRect.height + fm.getAscent()) / 2 - 1;
                    g2.drawString(distText, tx, ty);
                }
            }

            // ----- highlighted path + moving tricycle -----
            if (currentRoutes != null && !currentRoutes.isEmpty()
                    && currentPathIndex < currentRoutes.size()) {

                PathResult pr = currentRoutes.get(currentPathIndex);
                List<String> nodes = pr.path;

                java.util.List<Point> points = new ArrayList<>();
                for (String name : nodes) points.add(P.apply(name));

                double totalLen = 0;
                double[] segLen = new double[points.size() - 1];
                for (int i = 0; i < points.size() - 1; i++) {
                    Point a = points.get(i), b = points.get(i + 1);
                    double dx = b.x - a.x, dy = b.y - a.y;
                    segLen[i] = Math.sqrt(dx * dx + dy * dy);
                    totalLen += segLen[i];
                }

                double drawRatio = Math.max(0.0, Math.min(1.0, animationProgress));
                double drawnLen = totalLen * drawRatio;

                g2.setColor(new Color(255, 215, 0));
                g2.setStroke(new BasicStroke(Math.max(3.5f, h / 140f)));

                double remaining = drawnLen;
                int trikeX = -1, trikeY = -1;

                for (int i = 0; i < points.size() - 1; i++) {
                    Point a = points.get(i), b = points.get(i + 1);
                    double seg = segLen[i];
                    if (remaining >= seg) {
                        g2.drawLine(a.x, a.y, b.x, b.y);
                        remaining -= seg;
                        if (i == points.size() - 2 && drawRatio >= 1.0) {
                            trikeX = b.x;
                            trikeY = b.y;
                        }
                    } else {
                        double t = (seg == 0) ? 0 : remaining / seg;
                        int x = (int) Math.round(a.x + (b.x - a.x) * t);
                        int y = (int) Math.round(a.y + (b.y - a.y) * t);
                        g2.drawLine(a.x, a.y, x, y);
                        trikeX = x;
                        trikeY = y;
                        break;
                    }
                }

                if (trikeX >= 0 && trikeY >= 0) {
                    drawTricycleIcon(g2, trikeX, trikeY, Math.max(10, h / 40));
                }
            }

            // ----- nodes + labels -----
            g2.setFont(new Font("SansSerif", Font.BOLD, Math.max(11, h / 42)));
            Color labelTextColor = new Color(0x7F3C0F);
            FontMetrics fm2 = g2.getFontMetrics();
            for (String name : graph.nodes()) {
                Point p = P.apply(name);

                g2.setColor(Color.BLACK);
                g2.fillOval(p.x - nodeRadius, p.y - nodeRadius, 2 * nodeRadius, 2 * nodeRadius);
                if (name.equals(currentStart)) {
                    g2.setColor(Color.GREEN);
                    g2.fillOval(p.x - nodeRadius, p.y - nodeRadius, 2 * nodeRadius, 2 * nodeRadius);
                } else if (name.equals(currentDestination)) {
                    g2.setColor(Color.RED);
                    g2.fillOval(p.x - nodeRadius, p.y - nodeRadius, 2 * nodeRadius, 2 * nodeRadius);
                }

                Rectangle bgRect = labelRects.get(name);
                int textX = bgRect.x + 4;
                int textY = bgRect.y + fm2.getAscent() + 1;

                g2.setColor(new Color(255, 255, 255, 220));
                g2.fillRoundRect(bgRect.x, bgRect.y, bgRect.width, bgRect.height, 8, 8);

                g2.setColor(labelTextColor);
                g2.drawString(name, textX, textY);
            }

            g2.dispose();
        }

        // Simple drawn tricycle marker
        private void drawTricycleIcon(Graphics2D g2, int centerX, int centerY, int size) {
            int bodyWidth = size;
            int bodyHeight = (int) (size * 0.6);
            int halfW = bodyWidth / 2;
            int halfH = bodyHeight / 2;

            g2.setColor(new Color(127, 60, 15));
            g2.fillRoundRect(centerX - halfW, centerY - halfH, bodyWidth, bodyHeight, 6, 6);

            int wheelR = Math.max(3, size / 4);
            g2.setColor(Color.BLACK);
            g2.fillOval(centerX - halfW, centerY + halfH - wheelR / 2, wheelR, wheelR);
            g2.fillOval(centerX + halfW - wheelR, centerY + halfH - wheelR / 2, wheelR, wheelR);

            g2.setColor(Color.YELLOW);
            g2.fillOval(centerX + halfW - wheelR / 2, centerY - halfH, wheelR / 2, wheelR / 2);
        }
    }

    // Graph Map Layout
    private class GraphLayoutPanel extends JPanel {
        private MiniMapPanel mapPanel;
        GraphLayoutPanel(Image mapImg) {
            setLayout(new BorderLayout());
            setBackground(COLOR_BG_DARK);

            JPanel card = new JPanel(new BorderLayout());
            card.setBackground(COLOR_BG_CARD);
            card.setBorder(new EmptyBorder(24, 32, 32, 32));
            card.add(makeHeader(), BorderLayout.NORTH);

            mapPanel = new MiniMapPanel(mapImg);

            JPanel center = new JPanel(new BorderLayout());
            center.setOpaque(false);
            center.setBorder(new EmptyBorder(10, 40, 10, 40));

            JLabel label = new JLabel("Graph Map Layout");
            label.setFont(new Font("SansSerif", Font.BOLD, 18));
            label.setForeground(COLOR_TEXT);
            label.setHorizontalAlignment(SwingConstants.CENTER);

            JPanel legend = new JPanel(new FlowLayout(FlowLayout.LEFT, 12, 0));
            legend.setOpaque(false);
            legend.add(makeLegendItem(Color.GREEN, "Starting Point"));
            legend.add(makeLegendItem(Color.RED, "Destination"));
            legend.add(makeLegendItem(new Color(255, 215, 0), "Distance Travelled"));

            JPanel topRow = new JPanel(new BorderLayout());
            topRow.setOpaque(false);
            topRow.add(label, BorderLayout.CENTER);
            topRow.add(legend, BorderLayout.SOUTH);

            JPanel btnRow = new JPanel(new FlowLayout(FlowLayout.CENTER, 40, 16));
            btnRow.setOpaque(false);
            JButton detailsBtn = makePrimaryButton("Path Details");
            detailsBtn.addActionListener(e -> {
                pathDetailsPanel.refresh();
                cardLayout.show(mainPanel, "DETAILS");
            });
            btnRow.add(detailsBtn);

            center.add(topRow, BorderLayout.NORTH);
            center.add(mapPanel, BorderLayout.CENTER);
            center.add(btnRow, BorderLayout.SOUTH);

            card.add(center, BorderLayout.CENTER);
            add(card, BorderLayout.CENTER);
        }

        private JPanel makeLegendItem(Color color, String text) {
            JPanel panel = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 4));
            panel.setOpaque(false);
            JPanel dot = new JPanel();
            dot.setPreferredSize(new Dimension(12, 12));
            dot.setBackground(color);
            dot.setOpaque(true);
            dot.setBorder(BorderFactory.createLineBorder(Color.BLACK));
            JLabel label = new JLabel(text);
            label.setForeground(COLOR_TEXT);
            label.setFont(new Font("SansSerif", Font.PLAIN, 12));
            panel.add(dot);
            panel.add(label);
            return panel;
        }

        void refresh() { mapPanel.repaint(); }

        void startPathAnimation() { mapPanel.restartAnimation(); }
    }

    // ---------- actions ----------
    private void findRoutesFromHome() {
        currentStart = (String) homeStartCombo.getSelectedItem();
        currentDestination = (String) homeDestCombo.getSelectedItem();
        shortestRoutePanel.refresh();
        ((ShortestRoutePanel) shortestRoutePanel).recalcRoutes();
        graphLayoutPanel.refresh();
        graphLayoutPanel.startPathAnimation();
        cardLayout.show(mainPanel, "ROUTE");
    }

    private static class SimpleClickAdapter extends java.awt.event.MouseAdapter {
        private final Runnable r;
        SimpleClickAdapter(Runnable r) { this.r = r; }
        @Override public void mouseClicked(java.awt.event.MouseEvent e) { r.run(); }
    }

    // ---------- main ----------
    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> {
            TricycleRouteNavigatorUI ui = new TricycleRouteNavigatorUI();
            ui.setVisible(true);
        });
    }
}