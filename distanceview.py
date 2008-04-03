#!/usr/bin/python2.5
# -*- coding: utf-8 -*-

#
# © 2008 Joachim Breitner <mail@joachim-breitner.de>
#
#     This program is free software: you can redistribute it and/or modify
#     it under the terms of the GNU General Public License as published by
#     the Free Software Foundation, either version 3 of the License, or
#     (at your option) any later version.
# 
#     This program is distributed in the hope that it will be useful,
#     but WITHOUT ANY WARRANTY; without even the implied warranty of
#     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#     GNU General Public License for more details.
# 
#     You should have received a copy of the GNU General Public License
#     along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
#
# TODO:
# * Faster geometric algorithms (nearest point, containing facet)
# * Faster drawing (copying pixbufs to the X server)
# * Better morphs
# * Better interpolation
# 


import pygtk
import gtk
import gtk.glade
import gobject

import Numeric
import math
import pickle
import time
import os.path

selection_distance = 10

# wir = (294, 123)
# feth = (256, 203)
# gack = (267, 252)
# mitte = (394, 186)
# vor_inge = (370,107)
# klspieli = (396, 32)
# fuchs = (318, 49)
# polizeimensch = (360,225)
# doelker = (390,261)
# preiss_oben = (402,324)
# tunnel = (518,356)

# start = mitte
# 
# points = [
#     wir,
#     feth,
#     gack,
#     mitte,
#     klspieli,
#     fuchs,
#     polizeimensch,
#     doelker,
#     preiss_oben,
#     tunnel,
#     ]
# 
# graph = [
#     (wir,feth),
#     (feth,gack),
#     (gack,polizeimensch),
#     (polizeimensch,mitte),
#     (mitte,vor_inge),
#     (vor_inge,klspieli),
#     (fuchs,klspieli),
#     (fuchs,wir),
#     (polizeimensch,doelker),
#     (doelker,preiss_oben),
#     (preiss_oben, tunnel),
#     (tunnel,mitte),
#     ]

def dist2((x1,y1),(x2,y2)):
    return ((x1-x2)**2 + (y1-y2)**2)
def dist((x1,y1),(x2,y2)):
    return math.sqrt((x1-x2)**2 + (y1-y2)**2)
def find_footpoint((p1,p2),(x,y)):
    (x1,y1) = p1
    (x2,y2) = p2
    u = float((x-x1)*(x2-x1) + (y - y1)*(y2 - y1)) / float((x1-x2)**2 + (y1-y2)**2)
    if u<0: u=0
    if u>1: u=1
    return (int(round(x1 + u*(x2-x1))),
            int(round(y1 + u*(y2-y1))))
def convex(r, (r1,g1,b1), (r2,g2,b2)):
    return ((1-r) * r1 + r * r2,
            (1-r) * g1 + r * g2,
            (1-r) * b1 + r * b2)

class Graph(object):
    def __init__(self):
        self.vertices = []
        self.edges = []
        self.start = None

    def dump(self):
        return (self.vertices, self.edges, self.start)

    def load(self,dump):
        (self.vertices, self.edges, self.start) = dump

    def nearest_point(self, p):
        if self.vertices:
            return min(self.vertices, key=lambda v: dist(p,v))
        else:
            return (-100,-100)

    def alone(self,p):
        for (p1,p2) in self.edges:
            if p1 == p or p2 == p:
                return False
        return True

    def delete_vertex(self,p):
        assert self.alone(p)
        self.vertices.remove(p)

    def add_vertex(self, p):
        assert not p in self.vertices
        assert type(p[0]) == int and type(p[1]) == int
        if not self.vertices:
            self.start = p
        self.vertices.append(p)

    def has_edge(self,(p1,p2)):
        return (p1,p2) in self.edges or (p2,p1) in self.edges

    def toggle_edge(self,(p1,p2)):
        assert p1 in self.vertices and p2 in self.vertices
        if (p1,p2) in self.edges:
            self.edges.remove((p1,p2))
        elif (p2,p1) in self.edges:
            self.edges.remove((p2,p1))
        else:
            self.edges.append((p1,p2))
        
class DistanceView:
    def __init__(self):
        self.width = 300
        self.height = 300
        
        self.selected_d = 0
        self.last_update = 0
        self.point_selected = None
        self.hover_point = None

        self.image = gtk.DrawingArea()
        self.image.set_size_request(self.width, self.height)
        self.image.add_events(gtk.gdk.BUTTON_PRESS_MASK |
                        gtk.gdk.BUTTON_RELEASE_MASK |
                        gtk.gdk.EXPOSURE_MASK |
                        gtk.gdk.POINTER_MOTION_MASK)
        self.image.connect("expose_event",self.do_expose_event_orig)
        self.image.connect("button_press_event",self.do_button_press_event)
        self.image.connect("motion_notify_event",self.do_motion_notify_event)

        self.moved = gtk.DrawingArea()
        self.moved.set_size_request(self.width, self.height)
        self.moved.add_events(gtk.gdk.BUTTON_PRESS_MASK |
                        gtk.gdk.BUTTON_RELEASE_MASK |
                        gtk.gdk.EXPOSURE_MASK |
                        gtk.gdk.POINTER_MOTION_MASK)
        self.moved.connect("expose_event",self.do_expose_event_moved)

        hbox1 = gtk.HBox()
        hbox1.add(self.image)
        hbox1.add(self.moved)

        self.graph_edit = gtk.CheckButton('Edit graph')
        edit_help = gtk.Button('Edit help')
        edit_help.connect("clicked", self.show_edit_help)
        vbox_edit = gtk.VBox()
        vbox_edit.add(self.graph_edit)
        vbox_edit.add(edit_help)

        do_open = gtk.Button('Open Image')
        do_save = gtk.Button('Save graph')
        do_open.connect("clicked",self.do_open_dialog)
        do_save.connect("clicked",self.do_save_dialog)
        do_distance = gtk.Button('Calc Dist.')
        do_heightmap = gtk.Button('Calc Heightmap.')
        do_morph = gtk.Button('Calc Morph.')
        do_all = gtk.Button('Calc All.')
        do_distance.connect("clicked",self.do_recalc,self.recalc_distance)
        do_heightmap.connect("clicked",self.do_recalc,self.recalc_heightmap)
        do_morph.connect("clicked",self.do_recalc,self.recalc_morph)
        do_all.connect("clicked",self.do_recalc,self.recalc_all)
        self.do_buttons = [do_open, do_save, do_distance,
                           do_heightmap, do_all, do_morph]

        self.zoom = gtk.SpinButton()
        self.zoom.set_range(1,10)
        self.zoom.set_digits(1)
        self.zoom.set_increments(1,1)
        self.zoom.set_value(1)
        hbox_zoom = gtk.HBox()
        hbox_zoom.add(gtk.Label('Zoom:'))
        hbox_zoom.add(self.zoom)

        self.interpolator = gtk.combo_box_new_text()
        self.interpolators = {
                'Stripes': self.interpolate_stripes,
                'Blocks': self.interpolate_blocks,
                'None': self.interpolate_none,
            }
        keys = self.interpolators.keys()
        keys.sort()
        for k in keys:
            self.interpolator.append_text(k)
        self.interpolator.set_active(keys.index('None'))
        hbox_interpolator = gtk.HBox()
        hbox_interpolator.add(gtk.Label('Interpolation:'))
        hbox_interpolator.add(self.interpolator)
        
        vbox_morph = gtk.VBox()
        vbox_morph.add(hbox_interpolator)
        vbox_morph.add(hbox_zoom)

        self.penalty = gtk.SpinButton()
        self.penalty.set_range(1,10)
        self.penalty.set_increments(1,1)
        self.penalty.set_value(2)
        hbox_penalty = gtk.HBox()
        hbox_penalty.add(gtk.Label('Offroad penalty:'))
        hbox_penalty.add(self.penalty)

        vbox_dist = gtk.VBox()
        vbox_dist.add(hbox_penalty)

        self.show_heigthmap = gtk.CheckButton('Show heightmap')
        self.show_heigthmap.props.active = True
        self.show_heigthmap.connect('toggled', self.queue_draw)
        vbox_heightmap = gtk.VBox()
        vbox_heightmap.add(self.show_heigthmap)

        hbox2 = gtk.HBox()
        hbox2.pack_start(do_open, expand=False)
        hbox2.pack_start(do_save, expand=False)
        hbox2.pack_start(vbox_edit, expand=False)
        hbox2.pack_start(vbox_dist, expand=False)
        hbox2.pack_start(do_distance, expand=False)
        hbox2.pack_start(vbox_heightmap, expand=False)
        hbox2.pack_start(do_heightmap, expand=False)
        hbox2.pack_start(vbox_morph, expand=False)
        hbox2.pack_start(do_morph, expand=False)
        hbox2.pack_start(do_all, expand=False)
        
        self.status = gtk.Label("Status")
        
        self.progress = gtk.ProgressBar()
        self.reset_progress()

        hbox3 = gtk.HBox()
        hbox3.add(self.status)
        hbox3.add(self.progress)

        self.slider = gtk.HScale()
        self.slider.set_range(0,self.width+self.height)
        self.slider.connect("change_value",self.do_change_value)

        vbox = gtk.VBox()
        vbox.pack_start(hbox1, expand=True,fill=True)
        vbox.pack_start(self.slider, expand=False)
        vbox.pack_start(hbox2, expand=False)
        vbox.pack_start(hbox3, expand=False)

        self.window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        self.window.add(vbox)

        
        self.graph = Graph()
        self.d = None
        self.pixbuf = None
        self.pixbuf_heightmap = None
        self.pixbuf_moved = None
        self.moved_zoom = None
        if os.path.exists('Ehbühl.jpg'):
            self.load_files('Ehbühl.jpg')
        else:
            self.do_open_dialog(None)
        
        self.window.show_all()

    def do_expose_event_orig(self, widget, event):
        gc = widget.window.new_gc()
        gc.set_clip_rectangle(event.area)

        if self.pixbuf:
            widget.window.draw_pixbuf(gc, self.pixbuf, 0,0,0,0,-1,-1)
        if self.pixbuf_heightmap and self.show_heigthmap.props.active:
            widget.window.draw_pixbuf(gc, self.pixbuf_heightmap, 0,0,0,0,-1,-1)

        if (self.d
                and not self.graph_edit.props.active
                and not self.progress.props.sensitive):
            pb = self.equilines()
            widget.window.draw_pixbuf(gc, pb, 0,0,0,0,-1,-1)


        cr = widget.window.cairo_create()
        cr.rectangle(event.area.x, event.area.y, event.area.width, event.area.height)
        cr.clip()

        cr.set_source_rgba(0,0.8,0,0.8)
        for (s,t) in self.graph.edges:
            cr.move_to(*s)
            cr.line_to(*t)
            cr.stroke()
        for x,y in self.graph.vertices:
            cr.arc(x,y,2,0, 2 * math.pi)
            cr.fill()
        if self.graph.start:
            x,y = self.graph.start
            cr.arc(x,y,5,0, 2 * math.pi)
            cr.fill()

        if self.graph_edit.props.active and self.point_selected:
            x,y = self.point_selected
            cr.set_source_rgba(0,0,1,1)
            cr.arc(x,y,5,0, 2 * math.pi)
            cr.fill()
        
        if self.graph_edit.props.active and self.hover_point:
            x,y = self.hover_point
            cr.set_source_rgba(0.5,0.5,1,1)
            cr.arc(x,y,5,0, 2 * math.pi)
            cr.fill()

            if self.point_selected:
                if self.graph.has_edge((self.point_selected, self.hover_point)):
                    cr.set_source_rgba(1,0.5,0.5,1)
                else:
                    cr.set_source_rgba(0.5,0.5,1,1)
                cr.move_to(*self.point_selected)
                cr.line_to(*self.hover_point)
                cr.stroke()

    def do_expose_event_moved(self, widget, event):
        gc = widget.window.new_gc()
        gc.set_clip_rectangle(event.area)

        if self.pixbuf_moved:
            widget.window.draw_pixbuf(gc, self.pixbuf_moved, 0,0,0,0,-1,-1)

        cr = widget.window.cairo_create()
        cr.rectangle(event.area.x, event.area.y, event.area.width, event.area.height)
        cr.clip()
        
        if self.moved_zoom:
            z = self.moved_zoom

            cr.set_source_rgba(0,1,1,0.5)
            cr.arc(self.width/2, self.height/2, self.selected_d / z, 0, 2 * math.pi)
            cr.stroke()

    def do_button_press_event(self, widget, event):
        if self.graph_edit.props.active:
            p = (int(round(event.x)),int(round(event.y)))
            n = self.graph.nearest_point(p)

            if event.button == 1:  #left click
                if dist(n,p) > selection_distance:
                    self.graph.add_vertex(p)
                    self.point_selected = p
                else:
                    if self.point_selected == n:
                        self.point_selected = None
                    else:
                        self.point_selected = n

            elif event.button == 2: #middle click
                if dist(n,p) > selection_distance:
                    pass
                else:
                    self.graph.start = n

            elif event.button == 3: #right click
                if self.point_selected:
                    if dist(n,p) > selection_distance:
                        self.graph.add_vertex(p)
                        self.graph.toggle_edge((self.point_selected, p))
                        self.point_selected = p
                    else:
                        if n == self.point_selected:
                            if self.graph.alone(n):
                                self.graph.delete_vertex(n)
                                self.point_selected = None
                        else:
                            self.graph.toggle_edge((self.point_selected, n))
            self.queue_draw()

    def do_recalc(self, widget, func):
        func()
        self.queue_draw()

    def equilines(self):
        assert self.d
        pb = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, True, 8, self.width, self.height)
        el = pb.get_pixels_array()
        my_d = self.selected_d
        (s_x,s_y) = self.graph.start
        for x in range(max(0,int(s_x - my_d)), min(int(s_x + my_d), self.width)):
            for y in range(max(0,int(s_y - my_d)), min(int(s_y + my_d), self.height)):
                if my_d - 5 <=  self.d[x,y] <= my_d + 5:
                    a = 150
                    if my_d - 3 <=  self.d[x,y] <= my_d + 3:
                        a = 200
                        if my_d - 1 <=  self.d[x,y] <= my_d + 1:
                            a = 250
                    el[y,x,:]= (0,255,255,a)
        return pb

    def do_motion_notify_event(self, widget, event):
        if 0<=event.x<self.width and 0<=event.y<self.height:
            p = (int(round(event.x)),int(round(event.y)))
            if self.d:
                self.selected_d = self.d[p]
                self.status.set_text("(%d,%d): %d" % (event.x, event.y, self.selected_d))
                self.slider.set_value(self.selected_d)
               
                if not self.graph_edit.props.active and not self.progress.props.sensitive:
                    self.queue_draw()
        
            if self.graph_edit.props.active:
                n = self.graph.nearest_point(p)
                if dist(n,p) < selection_distance:
                    self.hover_point = n
                else:
                    self.hover_point = None
                self.queue_draw()
    
    def do_change_value(self, widget, scroll, value):
        value = int(value)
        if value != self.selected_d:
            self.selected_d = value
            self.status.set_text("Selected: %d" % (self.selected_d))
            self.queue_draw()
        return False

    def show_edit_help(self,widget):
        help = gtk.MessageDialog(parent = self.window,
                                type = gtk.MESSAGE_INFO,
                                buttons = gtk.BUTTONS_OK)
        help.props.text = '''Graph editing:
Left click to select/unselect a vertex.
Left click any where else to add a new vertex.
Middle click to select center vertex.
Right click on the selected vertex to delete it, if it has no edges anymore.
Right click on another vertex to add or remove the edge.
Right click anywhere ot adda vertex and an edge in one go.'''
        help.run()
        help.destroy()

    def queue_draw(self, widget=None):
        self.image.queue_draw()
        self.moved.queue_draw()

    def update_gui(self, pulse=False):
        now = time.time()
        if now - self.last_update > 0.1:
            if pulse:
                self.progress.pulse()
            while gtk.events_pending():
                gtk.main_iteration(False)
            self.last_update = now

    def prepare_progress(self):
        self.progress.props.sensitive = True
        self.progress.set_text('')
        self.progress.set_fraction(0)

        for button in self.do_buttons:
            button.props.sensitive = False

    def reset_progress(self):
        self.progress.props.sensitive = False
        self.progress.set_text('...idle...')
        self.progress.set_fraction(0)

        for button in self.do_buttons:
            button.props.sensitive = True
        self.update_gui()

    def recalc_distance(self):
        far = self.penalty.get_value_as_int() * (self.width + self.height)

        self.prepare_progress()
        self.progress.set_text('Preparing array')
        self.update_gui()
        d = Numeric.zeros((self.width,self.height), 'i')
        for x in range(self.width):
            self.update_gui(True)
            for y in range(self.height):
                d[x,y] = far

        d[self.graph.start] = 0
        todo = [self.graph.start]

        # unoptimized djikstra
        self.progress.set_text('Djikstra')
        self.update_gui()

        while todo:
            s = min(todo, key=lambda e: d[e])
            todo.remove(s)
            for t in ([t for (s2,t) in self.graph.edges if s2 == s ] +
                      [t for (t,s2) in self.graph.edges if s2 == s ]):
                if d[s] + dist(s,t) < d[t]:
                    d[t] = d[s] + dist(s,t)
                    todo.append(t)
            self.update_gui(True)

        self.progress.set_text('Off-Graph')
        for x in range(self.width):
            self.progress.set_fraction(float(x)/float(self.width))
            self.update_gui()
            for y in range(self.height):
                p = (x,y)
                if d[p]==far:
                    # Nearest footpoint:
                    #(p1,p2) = min(graph, key = lambda e: dist2(find_footpoint(e,p),p))
                    #footpoint = find_footpoint((p1,p2),p)
                    #if d[footpoint] == far:
                    #    d[footpoint] = min(d[p1] + dist(p1,footpoint),
                    #                       d[p2] + dist(p2,footpoint))
                    #d[p] = d[footpoint] + dist(p, footpoint)

                    # Best point:
                    #d[x,y] = min(map (lambda p1: d[p1] + 5*dist(p,p1), points))

                    # Best footpoint:
                    for (p1,p2) in self.graph.edges:
                        f = find_footpoint((p1,p2),p)
                        if d[f] == far:
                            d[f] = min(d[p1] + dist(p1,f), d[p2] + dist(p2,f))
                        d[p] = min(d[p], d[f] + self.penalty.get_value_as_int() * dist(f,p))

        #self.progress.set_text('Dumping data')
        #self.progress.set_fraction(0)
        #self.update_gui()
        #pickle.dump(d, file('distance_map.data','w'))

        self.d = d
        
        self.reset_progress()
    
    def recalc_heightmap(self):
        if self.d is None:
            self.recalc_distance()
        d = self.d
        
        self.prepare_progress()
        self.progress.set_text('Recreating heightmap')
        self.pixbuf_heightmap = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, True, 8, self.width, self.height)
        i = self.pixbuf_heightmap.get_pixels_array()
        #i = Numeric.zeros((self.height,self.width,4), 'b')
        for x in range(self.width):
            self.progress.set_fraction(float(x)/float(self.width))
            self.update_gui()
            for y in range(self.height):
                a = 255 - min(d[x,y]//3,255)
                i[y,x,:]= (255,0,0,a)

        #self.progress.set_text('Writing height data')
        #self.update_gui()
        #pickle.dump(i, file('height_map.data','w'))

        self.reset_progress()

    def recalc_morph(self):
        if self.d is None:
            self.recalc_distance()
        d = self.d

        z = self.zoom.get_value()

        self.prepare_progress()
        self.progress.set_text('Calculating transformation')
        f = Numeric.zeros((self.width,self.height,2),'i')
        (cx,cy) = (self.width/2, self.height/2)
        (sx,sy) = self.graph.start
        for x in range(self.width):
            self.progress.set_fraction(float(x)/float(self.width))
            self.update_gui()
            for y in range(self.height):
                p = (x,y)
                size = dist(p,self.graph.start) * z
                if size>0.05:
                    npx = int(round(cx + (x-sx)*d[p]/size))
                    npy = int(round(cy + (y-sy)*d[p]/size))
                    if 0<= npx < self.width and 0<= npy < self.height:
                        f[npx,npy,:] = (y,x)
                else:
                    f[cx,cy,:] = (y,x)
        
        #self.progress.set_text('Writing transformation data')
        #self.update_gui()
        #pickle.dump(f,file('function.data','w'))

        self.f = f

        self.reset_progress()

        self.prepare_progress()
        self.progress.set_text('Calculating Morphed Image')
        m = Numeric.zeros((self.height,self.width,3),'b')
        o = self.pixbuf.get_pixels_array()

        self.interpolate(o,m,f)

        #self.progress.set_text('Writing morphed image')
        #self.update_gui()
        #pickle.dump(m,file('output.data','w'))


        self.moved_zoom = z
        self.m = m
        self.pixbuf_moved = gtk.gdk.pixbuf_new_from_array(m, gtk.gdk.COLORSPACE_RGB, 8)
        self.reset_progress()

    def interpolate(self, o, m, f):
        choice = self.interpolator.get_active_text()
        self.interpolators[choice](o, m, f)

    def interpolate_blocks(self, o, m, f):
        for x in range(self.width):
            self.progress.set_fraction(float(x)/float(self.width))
            self.update_gui()

            for y in range(self.height):
                if f[x, y] != (0,0):
                    m[y,x] = o[f[x,y]]
                    #print "Pixel data found directly"
                else:
                    done = False
                    for i in range(1,3):
                        for tx in range(x-i,x+i+1):
                            if 0 <= tx < self.width:
                                for ty in range(y-i,y+i+1):
                                    if 0 <= ty < self.height:
                                        if f[tx, ty] != (0,0):
                                            m[y,x] = o[f[tx,ty]]
                                            done = True
                                            #print "Neighboring pixels asked (%d)" % i
                                            break
                            if done: break
                        if done: break
                    #if not done:
                    #    print "Could not find pixel to take color from."
                    #    m[y,x] = (255,255,0)

    def interpolate_stripes(self, o, m, f):
        for x in range(self.width):
            self.progress.set_fraction(float(x)/float(self.width))
            self.update_gui()

            prev = None
            for y in range(self.height):
                if f[x,y] != (0,0):
                    m[y,x] = o[f[x,y]]
                    if prev:
                        for my in range(prev+1,y):
                            m[my,x] = convex(
                                        float(my-prev)/float(y-prev),
                                        m[prev,x],
                                        m[y,x])
                    prev = y

    def interpolate_none(self, o, m, f):
        for x in range(self.width):
            self.progress.set_fraction(float(x)/float(self.width))
            self.update_gui()

            for y in range(self.height):
                if f[x,y] != (0,0):
                    m[y,x] = o[f[x,y]]

    def recalc_all(self):
        self.recalc_distance()
        self.recalc_heightmap()
        self.recalc_morph()

    def do_open_dialog(self, widget):
        dialog = gtk.FileChooserDialog(title = "Open Image",
                               parent =  self.window,
                               action = gtk.FILE_CHOOSER_ACTION_OPEN,
                               buttons = (gtk.STOCK_OK, gtk.RESPONSE_ACCEPT,
                                          gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT))

        if dialog.run():
            filename = dialog.get_filename()
            if filename:
                self.load_files(filename)
        dialog.destroy()

    def do_save_dialog(self, widget):
        assert self.filename, "No file open at the moment"
        self.save_files()
        help = gtk.MessageDialog(parent = self.window,
                                type = gtk.MESSAGE_INFO,
                                buttons = gtk.BUTTONS_OK)
        help.props.text = 'Graph and calculated data saved'
        help.run()
        help.destroy()

    def load_files(self, filename):
        self.pixbuf = gtk.gdk.pixbuf_new_from_file(filename)
        self.width = self.pixbuf.props.width
        self.height = self.pixbuf.props.height
        self.filename = filename

        self.graph = Graph()
        self.d = None
        self.pixbuf_heightmap = None
        self.pixbuf_moved = None
        self.moved_zoom = None

        if os.path.exists(filename+'.graph'):
            data = pickle.load(file(filename + '.graph'))
            self.graph.load(data)

        if os.path.exists(filename+'.data'):
            data = pickle.load(file(filename + '.data'))

            if 'd' in data:
                self.d = data['d']
            if 'i' in data and data['i']:
                self.pixbuf_heightmap = gtk.gdk.pixbuf_new_from_array(data['i'],
                                         gtk.gdk.COLORSPACE_RGB, 8)
            if 'm' in data and data['m']:
                self.m = data['m']
                self.pixbuf_moved = gtk.gdk.pixbuf_new_from_array(self.m,
                        gtk.gdk.COLORSPACE_RGB, 8)
            if 'mz' in data:
                self.moved_zoom = data['mz']
            if 'penalty' in data:
                self.penalty.set_value(data['penalty'])

    def save_files(self):
        assert self.filename, "No file open at the moment"

        pickle.dump(self.graph.dump(), file(self.filename + '.graph','w'))

        data = {}
        data['d'] = self.d
        if self.pixbuf_heightmap:
            data['i'] = self.pixbuf_heightmap.get_pixels_array()
        if self.pixbuf_moved:
            # Re-extracting pixel array from RGB without alpha
            # and re-inserting causes strange shift, so let’s
            # remember the array directly
            data['m'] = self.m
        data['mz'] = self.moved_zoom
        data['penalty'] = self.penalty.get_value_as_int()

        pickle.dump(data, file(self.filename + '.data','w'))

    def main(self):
        gtk.main()


if __name__ == "__main__":
    app = DistanceView()
    app.main()

# vim:ts=4:sw=4:sts=4:et

